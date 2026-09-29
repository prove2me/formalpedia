-- Prove2me | Definitions.Def_PolyhedralSOC_Shared_LorentzCone
-- name    : PolyhedralSOC_Shared_LorentzCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:44:22.886684+00:00
-- url     : https://prove2.me/theorems/c6ac57d6-34c3-4583-9a4a-4bb441ac790f
-- title:
--   Euclidean norm and the Lorentz cone $L^k$
-- statement:
--   For a vector $y=(y_1,\dots,y_k)\in\mathbb R^k$ let
--   $$\|y\|_2=\sqrt{y^Ty}=\sqrt{y_1^2+\dots+y_k^2}$$
--   be its Euclidean norm. The $(k+1)$-dimensional **Lorentz cone** (second-order cone, ice-cream cone) is
--   $$L^k=\{(y,t)\in\mathbb R^k\times\mathbb R \mid t\ge \|y\|_2\}.$$
--
--   This is the object that every result of the series approximates by polyhedral cones. It is shared by two missions of this series: I (upper bound: Theorem 1.1, p. 195, and the construction of §2, pp. 198–201) and II (lower bound: Proposition 3.1, p. 202, and its proof).
--
--   **Formalization Note** Vectors of $\mathbb R^k$ are functions `Fin k → ℝ`. The Euclidean norm is written out explicitly as `eucNorm y = √(∑ i, y i ^ 2)`, because the norm Mathlib puts on `Fin k → ℝ` is the sup norm, under which the cone would be polyhedral.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 193 (norm) and p. 194 (definition of L^k)

import Mathlib

namespace PolyhedralSOC.Shared

/-- The Euclidean norm `‖y‖₂ = √(yᵀy)` of a vector `y ∈ ℝ^k`
(Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), p. 193 (PDF p. 1)). Written out explicitly
because the norm Mathlib puts on `Fin k → ℝ` is the sup norm. -/
noncomputable def eucNorm {k : ℕ} (y : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i, y i ^ 2)

/-- The `(k+1)`-dimensional Lorentz cone `L^k = {(y, t) ∈ ℝ^k × ℝ | t ≥ ‖y‖₂}`
(Ben-Tal & Nemirovski 2001, p. 194 (PDF p. 2)). -/
def LorentzCone (k : ℕ) : Set ((Fin k → ℝ) × ℝ) :=
  {z | eucNorm z.1 ≤ z.2}

end PolyhedralSOC.Shared


