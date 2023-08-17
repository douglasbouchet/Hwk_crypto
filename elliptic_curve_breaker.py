import ast
import socket

from sage.all import EllipticCurve, GF, is_prime, CRT, mod
from lib.general_helper import parse_config
from functools import reduce

SCIPER = 000000 # TODO replace by student sciper. Removed as public repo

def create_Elliptic_curve(p, a, b):
    return EllipticCurve(GF(p), [a, b])


def question_3_a():
    Q3a_pp = parse_config('Q3a_pp', f'{SCIPER}-params.txt')
    Q3a_pk = parse_config('Q3a_pk', f'{SCIPER}-params.txt')
    a, b, p, x_G, y_G = Q3a_pp[0], Q3a_pp[1], Q3a_pp[2], Q3a_pp[3], Q3a_pp[4]
    pk_x, pk_y = Q3a_pk[0], Q3a_pk[1]
    E = create_Elliptic_curve(p, a, b)
    G = E(x_G, y_G)
    G_pk = E(pk_x, pk_y)
    sk = G.discrete_log(G_pk)
    assert sk * G == G_pk
    print('Sciper:{} Q3a_sk={}'.format(SCIPER, sk))
    return


def build_E_prime(p, a, b, x):
    # a point P = (x,y) on E' has order 2 if and only if y = 0
    x = x  # point (x,0) will have order 2 and will be on E'
    # we set b' such that the point (x,0) is on E'
    b_prime = (-(x**3) - a * x) % p
    return create_Elliptic_curve(p, a, b_prime)


def call_remote_oracle(x_p, y_p, seed):
    """Call the remote oracle with a given point

    Args:
        x_p (int): x coordinate of the point
        y_p (int): y coordinate of the point
        seed (int): seed to oracle queries

    Returns:
        str or Tuple(int): 'inf' if sk * point is infinity point, otw x and y coordinates of sk * point
    """
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as csock:
        csock.connect() # TODO I removed the address as the code is public 
        args = [str(seed), format(x_p, 'x'), format(y_p, 'x')]
        payload = ' '.join(args) + '\n'
        csock.send(payload.encode())  # call the oracle
        # chunk1: bytes = csock.recv(1000) # read a chunk of SIZE bytes
        chunk1: bytes = csock.recv(2000)  # read a chunk of SIZE bytes
        res = chunk1
        x_Q, y_Q = res.decode().split(' ')
        if x_Q == 'inf' and y_Q == 'inf':
            # return True
            return 'inf'
        else:
            x_Q, y_Q = int(x_Q, 16), int(y_Q, 16)
            return x_Q, y_Q


def find_small_order_points(E, max_order, n_trials, current_orders, points):
    """Find a point of order k on E
    Args:
        E (Elliptic Curve): Elliptic curve the points belongs to
        max_order (int): The maximum order of the points to be found
        n_trials (int): The number of trials for finding point of a given order
        current_orders (tuple(int,int)): The list of the current orders of the points found (prime number, power)
        points(Point[]): The list of points (we remove points with low order afterwards)
    Returns:
        point (Point[]): Points of order < max_order
    """
    E_order = E.order()
    E_factors = E_order.factor()
    # print(E_factors)
    P = E.random_element()
    bounded_factors = [
        factor for factor in E_factors if pow(factor[0], factor[1]) <= max_order
    ]
    # if factors of bounded_factors are not in current_orders or if they are but at a lower power,
    # we add them and their powers to the list of current orders. We can also remove the previous smaller factor
    for factor in bounded_factors:
        if factor[0] not in [order[0] for order in current_orders]:
            current_orders.append(factor)
        else:
            for order in current_orders:
                if order[0] == factor[0] and order[1] < factor[1]:
                    current_orders.remove(order)
                    current_orders.append(factor)

    for factor in bounded_factors:
        trials = 0
        order = pow(factor[0], factor[1])
        while trials < n_trials:
            P = E.random_element()
            Q = (E_order / order) * P
            if Q.order() == order:
                # we can add the point to our set of points
                points.append(Q)
                break
            trials += 1


def generate_small_order_points(p, a, b, n, n_curves=200, max_order=250):
    """Generate a set of orders with small orders.
    The orders of generated points are coprime (by the way we constuct our list of points)

    Args:
        p (int): modulo in Oracle Elliptic Curve
        a (int): a parameter of Oracle Elliptic Curve
        b (int): b parameter of Oracle Elliptic Curve
        n (int): secret key in Zn
        n_curves (int): number of elliptic curve whom we will try to find new points
        max_order (int): maximum order of a point (we need to keep this number low as we will need to
        perform at most 'order' queries to the oracle for a point of 'order')

    Returns:
        EllipticCurvePoint[]: Points of small coprimes orders
    """
    print('Generating points of small orders')
    current_orders = []
    points = []
    total_order = 0
    for i in range(3, n_curves):
        E_prime = build_E_prime(p, a, b, i)
        find_small_order_points(E_prime, max_order, 5, current_orders, points)
        total_order = reduce(
            lambda x, y: x * y, [factor[0] ** factor[1]
                                 for factor in current_orders]
        )
        if (n - 1) - total_order <= 0:
            print('we found enough points')
            break
    print('Total order: {}'.format(total_order))
    print('points:', len(points))
    # now we can get rid of the points whom their orders was replaced by one higher
    orders = [pow(factor[0], factor[1]) for factor in current_orders]
    keeped_points = []
    for point in points:
        # if the point order isn't in orders, we remove it
        if point.order() in orders:
            keeped_points.append(point)
            # remove point.order() from orders as we don't want to add 2 points with same order
            orders.remove(point.order())

    print('keeped_points:', len(keeped_points))
    keeped_points_order = reduce(
        lambda x, y: x * y, [point.order() for point in keeped_points]
    )
    assert total_order == keeped_points_order
    assert (n - 1) - total_order <= 0
    # verifiy that current_orders are only prime numbers
    for factor in current_orders:
        # the number are coprimes from how we construct them,
        # so we can then apply CRT
        assert is_prime(factor[0])
    return keeped_points


def compute_congruence_system(points, seed):
    """Given a set of points of small orders, we create a system of congruence equations using the remote oracle

    Args:
        points (EllipticCurvePoint): points with small order
        seed (int): seed to oracle queries

    Returns:
        list[Tuple[int]]: each element (a,b) of this list is the reminder (a) of sk modulo (b)
    """
    print(
        "Computing congruence system (you need to be on EPFL's network for oracle calls)"
    )
    congruence_system = []
    for i, point in enumerate(points):
        # print("{} over {}: order = {}".format(i,len(points), point.order()))
        xp, yp = point.xy()
        xp = int(xp)
        yp = int(yp)
        all_point_values = []
        for i in range(1, point.order()):
            all_point_values.append(i * point)
        res = call_remote_oracle(xp, yp, seed)
        if res == 'inf':
            # print("sk mod {} = {}".format(point.order(), 0))
            congruence_system.append([point.order(), 0])
        else:
            true_xp = res[0]
            true_yp = res[1]
            # we look which point is associated to return value in all_point_values
            for j, p in enumerate(all_point_values):
                p_x, p_y = p.xy()
                p_x = int(p_x)
                p_y = int(p_y)
                if p_x == true_xp and p_y == true_yp:
                    # print("sk mod {} = {}".format(point.order(), j+1))
                    congruence_system.append([point.order(), j + 1])
                    break
    return congruence_system


def compute_sk(congruence_system, n) -> int:
    """Solve the congruence system to find the secret key

    Args:
        congruence_system (list[Tuple[int]]): each element (a,b) of this list is the reminder (a) of sk modulo (b)
        n (int): secret key is in Zn

    Returns:
        int: the secret key (i.e solution of congruence system)
    """
    print('Computing the secret key')
    reminder_mod = [x[0] for x in congruence_system]
    reminder = [x[1] for x in congruence_system]
    crt_solution = CRT(reminder, reminder_mod)
    sk = mod(crt_solution, n - 1)
    print('Found secret key')
    return sk


def check_solution(p, a, b, secret_key, seed):
    """Check if the secret key is correct
    To verify we generate a random point belonging to the given Elliptic curve
    We then compare sk*This point and the return value of the oracle for the given point
    To be more sure, we test several points instead of a single one
    Assertion error if the secret key isn't correct

    Args:
        p (int): modulo in Oracle Elliptic Curve
        a (int): a parameter of Oracle Elliptic Curve
        b (int): b parameter of Oracle Elliptic Curve
        secret_key (int): the secret key
        seed (int): seed for oracle queries
    """
    print('Checking the secret key')
    Q3b_pp = parse_config('Q3b_pp', f'{SCIPER}-params.txt')
    E = create_Elliptic_curve(p, a, b)
    n_checks = 50  #  impossible to succeed if key isn't correct

    for i in range(n_checks):
        P = E.random_element()
        p_x, p_y = P.xy()
        oracle_response = call_remote_oracle(int(p_x), int(p_y), seed)
        local_x, local_y = (secret_key * P).xy()
        remote_x, remote_y = oracle_response[0], oracle_response[1]
        # if this assert isn't respected, this means the private key isn't the good one
        assert local_x == remote_x and local_y == remote_y
    print('The secret key is correct!')
    print('Sciper:{} Q3b_sk={}'.format(SCIPER, secret_key))


def question_3_b():
    seed = 0000000000000000000 # TODO fake seed as public repo 
    Q3b_pp = parse_config('Q3b_pp', f'{SCIPER}-params.txt')
    a, b, p, _, _, n, _ = (
        Q3b_pp[0],
        Q3b_pp[1],
        Q3b_pp[2],
        Q3b_pp[3],
        Q3b_pp[4],
        Q3b_pp[5],
        Q3b_pp[6],
    )
    # it is possible that this method fail (but unlikely), please increase n_curves and max_order (max x10)
    # if still don't work ask Douglas
    # keeped_points = generate_small_order_points(p, a, b, n, n_curves=200, max_order=250)
    # keeped_points = generate_small_order_points(p, a, b, n, n_curves=400, max_order=500)
    keeped_points = generate_small_order_points(
        p, a, b, n, n_curves=400, max_order=1000
    )  # stronger parameters but slower (less chances to fail)
    congruence_system = compute_congruence_system(keeped_points, seed)
    sk = compute_sk(congruence_system, n)
    check_solution(p, a, b, sk, seed)


if __name__ == '__main__':
    question_3_a()
    question_3_b()
