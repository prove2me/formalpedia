-- Prove2me | Definitions.Def_DeepQOperator_Supplement_Promise
-- name    : DeepQOperator_Supplement_Promise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:40:02.079604+00:00
-- url     : https://prove2.me/theorems/0a530f36-a565-4e60-9cb7-518d19f72f91
-- title:
--   The bounded continuous-address promise family (50)–(51)
-- statement:
--   Let $m\ge2$, $r=\lceil\log_2 m\rceil$, $n=2^r$, and let $c_i(v)=(-1)^{i\cdot v}$ ($0\le i\le m-1$, $v\in\{0,1\}^r$) be the Walsh code, with the dot product taken modulo two. The parameter $\theta=(a,z)\in\mathbb{R}^n\times\mathbb{R}^m$ is promised to lie in the nonconvex union of boxes
--   $$
--   P_{\mathrm{code}}=\bigcup_{i=0}^{m-1}\Big(\tfrac34 c_i+[-\tfrac18,\tfrac18]^n\Big)\times[0,1]^m .
--   $$
--   The three rows are
--   $$
--   A=\max_i\Big(\frac{c_i^{\mathsf T}a}{2n}+\frac{z_i}{4}\Big),\qquad B=\max_i\frac{c_i^{\mathsf T}a}{2n},\qquad C=\max\big(\{a_v\}_v\cup\{z_i\}_i\big).
--   $$
--   The responses $(1,0,0)$, $(0,1,0)$ and rewards $-\gamma/8$, $0$ give the contrast $g=\gamma(A-B-1/8)$, and the loss is (3). The displayed affine terms $c_i^{\mathsf T}a/(2n)+z_i/4$, $c_i^{\mathsf T}a/(2n)$, $a_v$ and $z_i$ are the raw sites.
--
--   This family supports Theorem 9 (exact raw-bit addressing).
--
--   **Formalization Note** Coordinates, Walsh words, Walsh scores, the row-C maximum and the row-B and coordinate sites are reused from the published family (6) (`DeepQOperator.Family`). Rows A and B here have no floor. $P_{\mathrm{code}}$ is the union of the boxes, not its convex hull.
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix F eqs. (50)–(51), p.27 (PDF p.30)

import Mathlib
import Definitions.Def_DeepQOperator_Family

open Finset

namespace DeepQOperator.Supplement

/-!
# The bounded continuous-address promise family (50)–(51)

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix F eqs. (50)–(51) p.27 (PDF p.30).

Let `r = ⌈log₂ m⌉`, `n = 2^r`, and `c_i(v) = (−1)^{i·v}` the Walsh code (`0 ≤ i ≤ m − 1`). The
parameter set is the nonconvex promise
`P_code = ⋃_{i=0}^{m−1} (3/4 c_i + [−1/8, 1/8]^n) × [0,1]^m`. For `θ = (a, z)` the rows are
`A = max_i (c_iᵀa/(2n) + z_i/4)`, `B = max_i c_iᵀa/(2n)`, `C = max({a_v}_v ∪ {z_i}_i)`; responses
`(1,0,0)`, `(0,1,0)` and rewards `−γ/8`, `0` give `g = γ(A − B − 1/8)`. The displayed affine terms
are the raw sites.

**Formalization Note.**
* The coordinates, Walsh words, Walsh scores `b_i = c_iᵀa/(2n)` (`bScore`), the row-C maximum
  (`rowC`), the row-B and coordinate raw sites (`siteB`, `siteC`) and `bellmanScore` are those of the
  published family (6) (`DeepQOperator.Family`). Rows A and B here have no floor.
* Rows A and B are real suprema over `Fin m`, i.e. maxima for `m ≥ 1`.
* `P_code` is the union of the boxes, not its convex hull.
-/

/-- The promise `P_code` of (50). -/
def promiseBox (m : ℕ) : Set (Coord m → ℝ) :=
  ⋃ i : Fin m, {θ | (∀ v : Addr m, θ (Sum.inl v) ∈
      Set.Icc (3 / 4 * walsh (rr m) i v - 1 / 8) (3 / 4 * walsh (rr m) i v + 1 / 8)) ∧
    ∀ j : Fin m, θ (Sum.inr j) ∈ Set.Icc (0 : ℝ) 1}

/-- Row A of (51): `max_i (c_iᵀa/(2n) + z_i/4)`. -/
noncomputable def pRowA (m : ℕ) (θ : Coord m → ℝ) : ℝ :=
  ⨆ i : Fin m, (bScore m i θ + θ (Sum.inr i) / 4)

/-- Row B of (51): `max_i c_iᵀa/(2n)`. -/
noncomputable def pRowB (m : ℕ) (θ : Coord m → ℝ) : ℝ := ⨆ i : Fin m, bScore m i θ

/-- The three row values `(A, B, C)` of (51). -/
noncomputable def pRows (m : ℕ) (θ : Coord m → ℝ) : Fin 3 → ℝ := ![pRowA m θ, pRowB m θ, rowC m θ]

/-- The score of decision `a`: `+` has response `(1,0,0)` and reward `−γ/8`, `−` has `(0,1,0)`, `0`. -/
noncomputable def pScore (m : ℕ) (γ : ℝ) (a : Bool) (θ : Coord m → ℝ) : ℝ :=
  if a then bellmanScore γ (-γ / 8) ![1, 0, 0] (pRows m θ) else bellmanScore γ 0 ![0, 1, 0] (pRows m θ)

/-- The decision loss (3) of the promise family. -/
noncomputable def pLoss (m : ℕ) (γ : ℝ) (a : Bool) (θ : Coord m → ℝ) : ℝ :=
  max (pScore m γ true θ) (pScore m γ false θ) - pScore m γ a θ

/-- The raw row-A site `c_iᵀa/(2n) + z_i/4`. -/
noncomputable def pSiteA (m : ℕ) (i : Fin m) : AffQuery (Coord m) :=
  (Sum.elim (fun v => walsh (rr m) i v / (2 * (nn m : ℝ))) (fun j => if j = i then 1 / 4 else 0), 0)

/-- The raw dictionary of (51): `c_iᵀa/(2n) + z_i/4`, `c_iᵀa/(2n)`, `a_v`, `z_i`. -/
noncomputable def promiseDictionary (m : ℕ) : Set (AffQuery (Coord m)) :=
  Set.range (pSiteA m) ∪ Set.range (siteB m) ∪ Set.range (siteC m)

end DeepQOperator.Supplement


