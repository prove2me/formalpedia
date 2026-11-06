-- Prove2me | Definitions.Def_ConstrSOSP_fsigma
-- name    : ConstrSOSP_fsigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:45.782333+00:00
-- url     : https://prove2.me/theorems/f6d6cec5-69f6-41af-93dd-a99d15aa8f48
-- title:
--   Biquintic Hermite interpolant $f_\sigma$ (17)
-- statement:
--   With $h(s)=6s^5-15s^4+10s^3$, $b_0=1-h$, $b_1=h$, $w_0(s)=s-6s^3+8s^4-3s^5$, $w_1(s)=-4s^3+7s^4-3s^5$, $q(s)=s^2(1-s)^2$, the interpolant on a unit cell is
--   $$
--   f_\sigma(x,y)=\sum_{i,j\in\{0,1\}}\big[z_{ij}b_i(x)b_j(y)+\xi_{ij}w_i(x)b_j(y)+\eta_{ij}b_i(x)w_j(y)\big]+\frac\sigma2\big(q(x)+q(y)\big),
--   $$
--   where $z_{ij}$ and $(\xi_{ij},\eta_{ij})$ are the value and gradient at corner $(i,j)$ and $\sigma$ the corner value of $f_{xx}=f_{yy}$.
--
--   **Formalization Note** The paper identifies (17) with the interpolant of §5.2 by uniqueness (p.34).
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), (16)–(17), p.33

import Mathlib

namespace ConstrSOSP

/-- **The biquintic Hermite interpolant (17) on a unit cell** (arXiv:2604.02285, 2 Nov 2026,
(16)–(17), p.33): with
`h(s) = 6s⁵ − 15s⁴ + 10s³`, `b₀(s) = 1 − h(s)`, `b₁(s) = h(s)`,
`w₀(s) = s − 6s³ + 8s⁴ − 3s⁵`, `w₁(s) = −4s³ + 7s⁴ − 3s⁵`, `q(s) = s²(1 − s)²`,
the polynomial
`f_σ(x, y) = Σ_{i,j∈{0,1}} [z_{ij} bᵢ(x) bⱼ(y) + ξ_{ij} wᵢ(x) bⱼ(y) + η_{ij} bᵢ(x) wⱼ(y)]
  + (σ/2)(q(x) + q(y))`,
in local coordinates `(x, y) ∈ [0, 1]²`, where `z_{ij}` is the value and `(ξ_{ij}, η_{ij})` the
gradient prescribed at the corner `(i, j)` and `σ` the common diagonal second derivative.

**Formalization Note** `z i j`, `ξ i j`, `η i j` are indexed by the corner `(i, j)`, `i` the
`x`-index. The paper identifies (17) with the interpolant (14)–(15) of §5.2 (p.34: "Uniqueness
therefore identifies it with the biquintic interpolant defined in Section 5.2"). -/
noncomputable def fsigma (σ : ℝ) (z ξ η : Fin 2 → Fin 2 → ℝ) (x y : ℝ) : ℝ :=
  let h : ℝ → ℝ := fun s => 6 * s ^ 5 - 15 * s ^ 4 + 10 * s ^ 3
  let bb : Fin 2 → ℝ → ℝ := fun i s => if i = 0 then 1 - h s else h s
  let w : Fin 2 → ℝ → ℝ := fun i s =>
    if i = 0 then s - 6 * s ^ 3 + 8 * s ^ 4 - 3 * s ^ 5 else -4 * s ^ 3 + 7 * s ^ 4 - 3 * s ^ 5
  let q : ℝ → ℝ := fun s => s ^ 2 * (1 - s) ^ 2
  (∑ i : Fin 2, ∑ j : Fin 2,
      (z i j * bb i x * bb j y + ξ i j * w i x * bb j y + η i j * bb i x * w j y)) +
    σ / 2 * (q x + q y)

end ConstrSOSP


