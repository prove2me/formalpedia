-- Prove2me | Definitions.Def_IntMul_HvdH_ExpApprox
-- name    : IntMul_HvdH_ExpApprox
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T21:59:56.106555+00:00
-- url     : https://prove2.me/theorems/ad93d80b-499c-49e1-a9f9-9748e03da720
-- title:
--   Fixed-point Taylor approximation of $e^z$ (Harvey–van der Hoeven §2.8)
-- statement:
--   Computable integer approximation of the complex exponential. Gaussian integers $a+bi$ are represented as pairs $(a,b)\in\mathbb Z^2$.
--
--   * `expTerm N x y j` is the $j$-th Taylor term of $2^N e^{z}$, $z=(x+iy)/2^N$, computed by the recurrence $t_0=2^N$, $t_{j+1}=\lfloor t_j\,(x+iy)/((j+1)2^N)\rfloor$ (floor applied to real and imaginary parts).
--   * `expApprox N K x y` $=\sum_{j<K}$ `expTerm N x y j` approximates $2^N e^{(x+iy)/2^N}$.
--   * `expBits n x y` approximates $2^n e^{(x+iy)/2^n}$: it scales the input to precision $2n+9$, sums $2n+13$ terms, and rounds each component to the nearest multiple of $2^{n+9}$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.8 (n-bit approximation of exp(z) for bounded z)

import Mathlib

/-! Fixed-point approximation of the complex exponential on the unit disc
(Harvey–van der Hoeven §2.8). Gaussian integers are represented as pairs `(re, im) : ℤ × ℤ`. -/

namespace IntMul.HvdH

open Finset

/-- Taylor terms of `2^N exp(z)` for `z = (x + i y) / 2^N`, computed by the recurrence
`t_{j+1} = ⌊t_j · (x + i y) / ((j+1) 2^N)⌋` (floor on each component), starting from `t_0 = 2^N`. -/
def expTerm (N : ℕ) (x y : ℤ) : ℕ → ℤ × ℤ
  | 0 => (2 ^ N, 0)
  | j + 1 =>
    let t := expTerm N x y j
    ((t.1 * x - t.2 * y) / ((j + 1) * 2 ^ N), (t.1 * y + t.2 * x) / ((j + 1) * 2 ^ N))

/-- Sum of the first `K` Taylor terms: an approximation of `2^N exp((x + i y) / 2^N)`. -/
def expApprox (N K : ℕ) (x y : ℤ) : ℤ × ℤ :=
  (∑ j ∈ range K, (expTerm N x y j).1, ∑ j ∈ range K, (expTerm N x y j).2)

/-- `n`-bit approximation of `exp((x + i y) / 2^n)`: work at precision `2n+9` with `2n+13` terms,
then round each component to the nearest multiple of `2^{n+9}`. -/
def expBits (n : ℕ) (x y : ℤ) : ℤ × ℤ :=
  let e := expApprox (2 * n + 9) (2 * n + 13) (x * 2 ^ (n + 9)) (y * 2 ^ (n + 9))
  ((e.1 + 2 ^ (n + 8)) / 2 ^ (n + 9), (e.2 + 2 ^ (n + 8)) / 2 ^ (n + 9))

end IntMul.HvdH


