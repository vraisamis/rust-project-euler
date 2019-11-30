#![allow(dead_code)]
#[allow(dead_code)]
macro_rules! input {
    (source = $s:expr, $($r:tt)*) => {
        let mut iter = $s.split_whitespace();
        let mut next = || { iter.next().unwrap() };
        input_inner!{next, $($r)*}
    };
    ($($r:tt)*) => {
        let stdin = std::io::stdin();
        let mut bytes = std::io::Read::bytes(std::io::BufReader::new(stdin.lock()));
        let mut next = move || -> String{
            bytes
                .by_ref()
                .map(|r|r.unwrap() as char)
                .skip_while(|c|c.is_whitespace())
                .take_while(|c|!c.is_whitespace())
                .collect()
        };
        input_inner!{next, $($r)*}
    };
}

#[allow(dead_code)]
macro_rules! input_inner {
    ($next:expr) => {};
    ($next:expr, ) => {};

    ($next:expr, $var:ident : $t:tt $($r:tt)*) => {
        let $var = read_value!($next, $t);
        input_inner!{$next $($r)*}
    };

    ($next:expr, mut $var:ident : $t:tt $($r:tt)*) => {
        let mut $var = read_value!($next, $t);
        input_inner!{$next $($r)*}
    };
}

#[allow(dead_code)]
macro_rules! read_value {
    ($next:expr, ( $($t:tt),* )) => {
        ( $(read_value!($next, $t)),* )
    };

    ($next:expr, [ $t:tt ; $len:expr ]) => {
        (0..$len).map(|_| read_value!($next, $t)).collect::<Vec<_>>()
    };

    ($next:expr, chars) => {
        read_value!($next, String).chars().collect::<Vec<char>>()
    };

    ($next:expr, usize1) => {
        read_value!($next, usize) - 1
    };

    ($next:expr, $t:ty) => {
        $next().parse::<$t>().expect("Parse error")
    };
}

fn main() {
    println!("answer12 = {}", solve12());
}

fn solve1() -> u64 {
    (3..1000)
        .into_iter()
        .filter(|i| i % 3 == 0 || i % 5 == 0)
        .fold(0, |cum, a| cum + a)
}

fn solve2() -> u64 {
    let th = 4_000_000;
    let mut sum = 0;
    let mut cur = (1, 1);
    let next = move |(a, b)| {
        let n = a + b;
        if n <= th {
            Some((b, n))
        } else {
            None
        }
    };
    while let Some(nc) = next(cur) {
        if nc.1 % 2 == 0 {
            sum += nc.1;
        }
        cur = nc;
    }
    sum
}

fn primes(n: usize) -> Vec<usize> {
    if n < 2 {
        return vec![];
    }

    let mut v = vec![true; n];
    v[0] = false;
    v[1] = false;

    let mut result = vec![];
    for i in 2..n {
        if v[i] {
            result.push(i);
            let mut j = 2 * i;
            while j < n {
                v[j] = false;
                j += i;
            }
        }
    }

    result
}

fn solve3() -> u64 {
    let target = 600851475143u64;
    for p in primes((target as f64).sqrt() as usize).into_iter().rev() {
        let p = p as u64;
        if target % p == 0 {
            return p;
        }
    }
    0
}

fn solve4() -> u64 {
    use std::collections::BinaryHeap;
    let mut heap = BinaryHeap::new();
    for i in 100..1000 {
        for j in i..1000 {
            heap.push(i * j);
        }
    }
    while let Some(v) = heap.pop() {
        let vs = v.to_string();
        let rvs = vs.chars().rev().collect::<String>();
        if vs == rvs {
            return v;
        }
    }
    0
}

fn gcd(a: u64, b: u64) -> u64 {
    use std::cmp::{max, min};
    let (a, b) = (min(a, b), max(a, b));
    match a {
        0 => b,
        _ => gcd(b % a, a),
    }
}

fn solve5() -> u64 {
    (2..21)
        .into_iter()
        .rev()
        .fold(1, |n, v| if n % v == 0 { n } else { n * v / gcd(v, n) })
}

fn solve6() -> u64 {
    let mut sqsum = 0;
    let mut sum = 0;
    for i in 1..101 {
        sqsum += i * i;
        sum += i;
    }
    sum * sum - sqsum
}

fn solve7() -> u64 {
    let n = 10_001;
    let mut i = 1;
    let mut p = vec![];
    while p.len() < n {
        p = primes(10u32.pow(i) as usize);
        i += 1;
    }
    p[n - 1] as u64
}

fn solve8() -> u64 {
    use std::collections::VecDeque;
    use std::cmp::max;
    let mut vv: Vec<u64> = "7316717653133062491922511967442657474235534919493496983520312774506326239578318016984801869478851843858615607891129494954595017379583319528532088055111254069874715852386305071569329096329522744304355766896648950445244523161731856403098711121722383113622298934233803081353362766142828064444866452387493035890729629049156044077239071381051585930796086670172427121883998797908792274921901699720888093776657273330010533678812202354218097512545405947522435258490771167055601360483958644670632441572215539753697817977846174064955149290862569321978468622482839722413756570560574902614079729686524145351004748216637048440319989000889524345065854122758866688116427171479924442928230863465674813919123162824586178664583591245665294765456828489128831426076900422421902267105562632111110937054421750694165896040807198403850962455444362981230987879927244284909188845801561660979191338754992005240636899125607176060588611646710940507754100225698315520005593572972571636269561882670428252483600823257530420752963450".chars().map(|c| c.to_string().parse().unwrap()).collect();
    let vv2 = vv.split_off(13);
    let mut v = VecDeque::from(vv);
    let fcum = |q: &VecDeque<_>| q.iter().fold(1, |cum, k| cum * k);
    let mut m = fcum(&v);
    for k in vv2 {
        v.pop_front();
        v.push_back(k);
        m = max(m, fcum(&v));
    }
    m
}

fn solve9() -> u64 {
    let n = 1000;
    for a in 1..n - 1 {
        for b in 1..n - 1 {
            let ab = a + b;
            if ab >= n {
                break;
            }
            let c = n - ab;
            if a * a + b * b == c * c {
                return a * b * c;
            }
        }
    }
    0
}

fn solve10() -> u64 {
    primes(2_000_000).iter().fold(0, |sum, a| sum + a) as u64
}

fn solve11() -> u64 {
    let s = "08 02 22 97 38 15 00 40 00 75 04 05 07 78 52 12 50 77 91 08
49 49 99 40 17 81 18 57 60 87 17 40 98 43 69 48 04 56 62 00
81 49 31 73 55 79 14 29 93 71 40 67 53 88 30 03 49 13 36 65
52 70 95 23 04 60 11 42 69 24 68 56 01 32 56 71 37 02 36 91
22 31 16 71 51 67 63 89 41 92 36 54 22 40 40 28 66 33 13 80
24 47 32 60 99 03 45 02 44 75 33 53 78 36 84 20 35 17 12 50
32 98 81 28 64 23 67 10 26 38 40 67 59 54 70 66 18 38 64 70
67 26 20 68 02 62 12 20 95 63 94 39 63 08 40 91 66 49 94 21
24 55 58 05 66 73 99 26 97 17 78 78 96 83 14 88 34 89 63 72
21 36 23 09 75 00 76 44 20 45 35 14 00 61 33 97 34 31 33 95
78 17 53 28 22 75 31 67 15 94 03 80 04 62 16 14 09 53 56 92
16 39 05 42 96 35 31 47 55 58 88 24 00 17 54 24 36 29 85 57
86 56 00 48 35 71 89 07 05 44 44 37 44 60 21 58 51 54 17 58
19 80 81 68 05 94 47 69 28 73 92 13 86 52 17 77 04 89 55 40
04 52 08 83 97 35 99 16 07 97 57 32 16 26 26 79 33 27 98 66
88 36 68 87 57 62 20 72 03 46 33 67 46 55 12 32 63 93 53 69
04 42 16 73 38 25 39 11 24 94 72 18 08 46 29 32 40 62 76 36
20 69 36 41 72 30 23 88 34 62 99 69 82 67 59 85 74 04 36 16
20 73 35 29 78 31 90 01 74 31 49 71 48 86 81 16 23 57 05 54
01 70 54 71 83 51 54 69 16 92 33 48 61 43 52 01 89 19 67 48".to_string();
    input!{
        source = s,
        aa : [[u64; 20]; 20]
    }
    let fsum = |a, b, c, d| a * b * c * d;
    // println!("{:?}", aa);
    // horizonal
    let h: u64 = aa.iter().filter_map(|row| {
        (0..row.len() - 3).into_iter().map(|i| {
            fsum(row[i], row[i + 1], row[i + 2], row[i + 3])
        }).max()
    }).max().unwrap();
    // vertical
    let v: u64 = {
        use std::cmp::max;
        let mut m = 0;
        for col in 0..aa[0].len() {
            for row in 0..aa.len() - 3 {
                let v = fsum(aa[row][col], aa[row + 1][col], aa[row + 2][col], aa[row + 3][col]);
                m = max(m, v);
            }
        }
        m
    };
    let d = {
        use std::cmp::max;
        let mut m = 0;
        for row in 0..aa.len() - 3 {
            for col in 0..aa[0].len() - 3{
                let v1 = fsum(aa[row][col], aa[row + 1][col + 1], aa[row + 2][col + 2], aa[row + 3][col + 3]);
                let v2 = fsum(aa[row][col + 3], aa[row + 1][col + 2], aa[row + 2][col + 1], aa[row + 3][col]);
                m = max(m, v1);
                m = max(m, v2);
            }
        }
        m
    };
    *vec![h, v, d].iter().max().unwrap()
}

fn primes2(ps: Option<Vec<usize>>, n: usize) -> Vec<usize> {
    if n < 2 {
        return vec![];
    }
    let mut ps = match ps {
        Some(p) => p,
        None => vec![2]
    };
    let last = ps[ps.len() - 1];

    let fill = |iv: &mut Vec<_>, ik| {
        let mut j = 2 * ik;
        while j < last {
            j += ik;
        }
        while j < n {
            iv[j - last] = false;
            j += ik;
        }
    };
    let mut v = vec![true; n - last];
    for &k in ps.iter() {
        fill(&mut v, k);
    }

    let mut result = vec![];
    for i in 1..n - last {
        if v[i] {
            result.push(i + last);
            fill(&mut v, i + last);
        }
    }

    ps.append(&mut result);
    ps 
}

fn count_dividors(n: usize, ps: &Vec<usize>) -> usize {
    let mut n = n as usize;
    // let ps = primes(n + 1);
    let mut v: Vec<(usize, usize)> = vec![];
    for p in ps {
        let mut k = 0;
        while n % p == 0 {
            n = n / p;
            k += 1;
        }
        if k > 0 {
            v.push((p.clone(), k));
        }
    }
    v.into_iter().fold(1, |cum, (_, k)| cum * (k + 1))
}

fn solve12() -> u64 {
    // speed issue
    let mut i = 1;
    let mut sum = 0;
    let n = 500;
    let mut ps = vec![2];
    loop {
        sum += i;
        ps = primes2(Some(ps), (sum + 1) as usize);
        let d = count_dividors(sum as usize, &ps);
        if d > n {
            break;
        }
        i += 1;
    }
    sum
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn prime_test() {
        let prime_under_19 = primes(19);
        assert_eq!(prime_under_19, vec![2, 3, 5, 7, 11, 13, 17]);
        let prime_under_20 = primes(20);
        assert_eq!(prime_under_20, vec![2, 3, 5, 7, 11, 13, 17, 19]);
    }

    #[test]
    fn prime2_test() {
        let prime_under_19 = primes2(None, 19);
        assert_eq!(prime_under_19, vec![2, 3, 5, 7, 11, 13, 17]);
        let prime_under_20 = primes2(None, 20);
        assert_eq!(prime_under_20, vec![2, 3, 5, 7, 11, 13, 17, 19]);
        let prime_under_10 = primes2(None, 10);
        let prime_under_30 = primes2(Some(prime_under_10), 30);
        assert_eq!(prime_under_30, vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]);
    }

    #[test]
    fn gcd_test() {
        assert_eq!(1, gcd(1, 20));
        assert_eq!(1, gcd(20, 1));
        assert_eq!(3, gcd(21, 12));

        assert_eq!(1, gcd(20, 1));
    }

    #[test]
    fn count_dividors_test() {
        let ps = primes(20);
        for i in ps {
            assert_eq!(count_dividors(i), 2);
        }
        assert_eq!(count_dividors(12), 6);
    }
}
