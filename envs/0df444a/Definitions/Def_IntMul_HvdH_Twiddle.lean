-- Prove2me | Definitions.Def_IntMul_HvdH_Twiddle
-- name    : IntMul_HvdH_Twiddle
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T22:08:54.498975+00:00
-- url     : https://prove2.me/theorems/efed0926-8040-42fc-8407-c2b2100ba44d
-- title:
--   Fixed-point roots of unity $e^{2\pi ij/k}$ (Harvey–van der Hoeven Lemma 2.12)
-- statement:
--   Computable approximation of the roots of unity $e^{2\pi ij/k}$, with Gaussian integers represented as pairs $(a,b)\in\mathbb Z^2$.
--
--   * `mulI` and `conjZ` are multiplication by $i$ and complex conjugation on $\mathbb Z[i]$.
--   * `octExp n k a` approximates $2^n e^{i\pi a/(4k)}$ for $0\le a\le k$: the angle $\pi a/(4k)$ is computed to $n+4$ bits from `piBits`, exponentiated with `expBits`, and rounded to precision $n$.
--   * `twiddle n k j` approximates $2^n e^{2\pi ij/k}$: with $j'=j\bmod k$ and $8j'=qk+r$, it returns $i^m\cdot$`octExp n k r` if $q=2m$ and $i^{m+1}\cdot\overline{\text{octExp } n\, k\,(k-r)}$ if $q=2m+1$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.12 (complex exponentials e^{2 pi i j/k})

import Definitions.Def_IntMul_HvdH_Numeric
import Definitions.Def_IntMul_HvdH_ExpApprox

/-! Fixed-point roots of unity `e^{2πij/k}` (Harvey–van der Hoeven Lemma 2.12), computed by
reduction to an angle in `[0, π/4]` followed by the Taylor approximation `expBits`. -/

namespace IntMul.HvdH

/-- Multiplication by `i` on Gaussian integers `(re, im)`. -/
def mulI (p : ℤ × ℤ) : ℤ × ℤ := (-p.2, p.1)

/-- Complex conjugation on Gaussian integers `(re, im)`. -/
def conjZ (p : ℤ × ℤ) : ℤ × ℤ := (p.1, -p.2)

/-- Approximation of `2^n e^{iπa/(4k)}` for `0 ≤ a ≤ k`: the angle is computed to `n+4` bits from
`piBits`, exponentiated with `expBits`, and rounded to precision `n`. -/
def octExp (n k a : ℕ) : ℤ × ℤ :=
  let φ : ℤ := piBits (n + 4) * a / (4 * k)
  let u := expBits (n + 4) 0 φ
  ((u.1 + 2 ^ 3) / 2 ^ 4, (u.2 + 2 ^ 3) / 2 ^ 4)

/-- Approximation of `2^n e^{2πij/k}`. With `j' = j mod k` and `8j' = qk + r`, `q = 2m` or
`q = 2m+1`, use `e^{2πij/k} = i^m e^{iπr/(4k)}` or `i^{m+1} conj(e^{iπ(k-r)/(4k)})`. -/
def twiddle (n k j : ℕ) : ℤ × ℤ :=
  let j' := j % k
  let q := 8 * j' / k
  let r := 8 * j' % k
  if q % 2 = 0 then mulI^[q / 2] (octExp n k r)
  else mulI^[q / 2 + 1] (conjZ (octExp n k (k - r)))

end IntMul.HvdH


