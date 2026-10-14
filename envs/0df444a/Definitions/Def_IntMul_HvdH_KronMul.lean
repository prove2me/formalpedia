-- Prove2me | Definitions.Def_IntMul_HvdH_KronMul
-- name    : IntMul_HvdH_KronMul
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-11T22:48:45.167515+00:00
-- url     : https://prove2.me/theorems/5f947db8-feee-4566-bea9-a9afdbe678db
-- title:
--   Kronecker substitution and multiplication in $\mathbb C[y]/(y^r+1)$ (Harvey–van der Hoeven Lemma 2.5)
-- statement:
--   Computable list algorithms for Lemma 2.5. Coefficient lists are read constant term first.
--
--   * `kpack B c` $=\sum_i c_iB^i$ packs coefficients into one integer, and `kunpack B n W` reads off $n$ balanced base-$B$ digits $c_i\in[-B/2,B/2)$.
--   * `polyMul a b` is the schoolbook product, whose $k$-th coefficient is $\sum_{i\le k}a_ib_{k-i}$.
--   * `negFold r l` reduces modulo $y^r+1$, and `listAdd`/`listSub` act coefficientwise.
--   * `mulRSpec p r U₀ U₁ V₀ V₁` is the specification of Lemma 2.5. It computes $W_0=(U_0V_0-U_1V_1)\bmod (y^r+1)$ and $W_1=(U_0V_1+U_1V_0)\bmod (y^r+1)$, then divides each coefficient by $2^pr$, rounding towards zero.
--   * `kronMul p r a b` multiplies two length-$r$ lists by Kronecker substitution at $B=2^{3p}$, using one integer product. `mulR` is `mulRSpec` with its four polynomial products computed by `kronMul`.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.5 (Kronecker substitution)

import Mathlib

/-! Kronecker substitution and fixed-point multiplication in `R = ℂ[y]/(y^r + 1)`
(Harvey–van der Hoeven Lemma 2.5). Polynomials are lists of coefficients, constant term first. -/

namespace IntMul.HvdH

/-- Evaluate a coefficient list at `B`: `kpack B [c₀, c₁, …] = c₀ + c₁ B + ⋯`. -/
def kpack (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | c :: cs => c + B * kpack B cs

/-- Read off `n` balanced base-`B` digits (each in `[-B/2, B/2)`), least significant first. -/
def kunpack (B : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n + 1, W =>
    let c := (W + B / 2) % B - B / 2
    c :: kunpack B n ((W - c) / B)

/-- Schoolbook product of coefficient lists: the `k`-th coefficient is `∑_{i ≤ k} aᵢ b_{k-i}`. -/
def polyMul (a b : List ℤ) : List ℤ :=
  (List.range (a.length + b.length - 1)).map
    (fun k => ∑ i ∈ Finset.range (k + 1), a.getD i 0 * b.getD (k - i) 0)

/-- Reduce a coefficient list modulo `y^r + 1`: `i ↦ lᵢ - l_{i+r}` (enough for length `≤ 2r`). -/
def negFold (r : ℕ) (l : List ℤ) : List ℤ :=
  (List.range r).map (fun i => l.getD i 0 - l.getD (i + r) 0)

/-- Coefficientwise sum and difference of two coefficient lists of length `n`. -/
def listAdd (n : ℕ) (a b : List ℤ) : List ℤ := (List.range n).map (fun i => a.getD i 0 + b.getD i 0)
def listSub (n : ℕ) (a b : List ℤ) : List ℤ := (List.range n).map (fun i => a.getD i 0 - b.getD i 0)

/-- Lemma 2.5, specification: with `2^p u = U₀ + i U₁` and `2^p v = V₀ + i V₁` in `ℤ[i][y]/(y^r+1)`,
the coefficients of `2^{2p} r · (uv / r) = W₀ + i W₁`, each divided by `2^p r` with rounding towards
zero. -/
def mulRSpec (p r : ℕ) (U0 U1 V0 V1 : List ℤ) : List (ℤ × ℤ) :=
  let W0 := negFold r (listSub (2 * r - 1) (polyMul U0 V0) (polyMul U1 V1))
  let W1 := negFold r (listAdd (2 * r - 1) (polyMul U0 V1) (polyMul U1 V0))
  (List.range r).map (fun l => ((W0.getD l 0).tdiv (2 ^ p * r), (W1.getD l 0).tdiv (2 ^ p * r)))

/-- Product of two length-`r` coefficient lists by Kronecker substitution at `2^{3p}`:
one integer multiplication, then `2r - 1` balanced digits. -/
def kronMul (p r : ℕ) (a b : List ℤ) : List ℤ :=
  kunpack (2 ^ (3 * p)) (2 * r - 1) (kpack (2 ^ (3 * p)) a * kpack (2 ^ (3 * p)) b)

/-- Lemma 2.5, algorithm: as `mulRSpec`, with the four polynomial products computed by
Kronecker substitution (four integer multiplications of `3rp`-bit integers). -/
def mulR (p r : ℕ) (U0 U1 V0 V1 : List ℤ) : List (ℤ × ℤ) :=
  let W0 := negFold r (listSub (2 * r - 1) (kronMul p r U0 V0) (kronMul p r U1 V1))
  let W1 := negFold r (listAdd (2 * r - 1) (kronMul p r U0 V1) (kronMul p r U1 V0))
  (List.range r).map (fun l => ((W0.getD l 0).tdiv (2 ^ p * r), (W1.getD l 0).tdiv (2 ^ p * r)))

end IntMul.HvdH


