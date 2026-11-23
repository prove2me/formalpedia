-- Prove2me | Definitions.Def_RobustSAA_Discrete_Supplement_Cones
-- name    : RobustSAA_Discrete_Supplement_Cones
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:37:02.698285+00:00
-- url     : https://prove2.me/theorems/efcd243a-025f-4abe-96cf-e6f70592984b
-- title:
--   §5.1–5.2 — the cones $C^3_{SOC}$, $C_{XC}$, $C^{k}_{SOC}$, dual cones and conic optimal values
-- statement:
--   This file fixes the cones used in the conic reformulations of §5 of Bertsimas, Gupta and Kallus.
--
--   1. The three-dimensional second-order cone of Theorem 8, $C^3_{SOC}=\{(x,y,z)\in\mathbb R^3: x\ge\sqrt{y^2+z^2}\}$.
--   2. The exponential cone of Theorem 8, $C_{XC}=\operatorname{closure}\{(x,y,z): y e^{x/y}\le z,\ y>0\}$, the closure being taken in $\mathbb R^3$.
--   3. The second-order cone $C^{k+1}_{SOC}=\{(x_0,x)\in\mathbb R\times\mathbb R^k: x_0\ge\|x\|_2\}$, written on coordinates indexed by $\{\mathrm{none}\}\cup\iota$ with the leading coordinate first.
--   4. The dual cone $K^*=\{y: y^\top z\ge0\ \text{for all } z\in K\}$ (p. 18).
--   5. A convex cone: a convex set closed under multiplication by nonnegative scalars.
--   6. The optimal value of a minimization problem: $V$ is the minimum of a problem whose feasible objective values form $D\subseteq\mathbb R$ when $V=\inf D$ in the extended reals ($V=+\infty$ if $D=\emptyset$) and, if $D\neq\emptyset$, $V$ is attained by some element of $D$.
--
--   These objects are shared by Theorems 8, 10, 11 and 12.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Theorem 8 p. 16 (cones), §5.2 p. 17 (canonical cones), p. 18 (dual cone)

import Mathlib

namespace RobustSAA.Discrete.Supplement

open scoped BigOperators

/-- The three-dimensional second-order cone of Theorem 8 (p. 16):
`C³_SOC = {(x, y, z) ∈ ℝ³ : x ≥ √(y² + z²)}`. -/
def soc3 : Set (ℝ × ℝ × ℝ) :=
  {v | Real.sqrt (v.2.1 ^ 2 + v.2.2 ^ 2) ≤ v.1}

/-- The exponential cone of Theorem 8 (p. 16):
`C_XC = closure {(x, y, z) : y e^{x/y} ≤ z, y > 0}` (closure in `ℝ³`). -/
def expCone : Set (ℝ × ℝ × ℝ) :=
  closure {v | 0 < v.2.1 ∧ v.2.1 * Real.exp (v.1 / v.2.1) ≤ v.2.2}

/-- The second-order cone on coordinates `Option ι`: the coordinate `none` is the leading
coordinate `x₀` and the coordinates `some i` are the remaining ones,
`{v : x₀ ≥ ‖(vᵢ)ᵢ‖₂}`. With `ι = Fin N` this is `C^{N+1}_SOC`; with `ι = Option (Fin N)` it is
`C^{N+2}_SOC` (p. 17). -/
def soc (ι : Type*) [Fintype ι] : Set (Option ι → ℝ) :=
  {v | Real.sqrt (∑ i, v (some i) ^ 2) ≤ v none}

/-- The dual cone `K* = {y : yᵀz ≥ 0 for all z ∈ K}` (p. 18). -/
def dualCone {ι : Type*} [Fintype ι] (K : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {y | ∀ z ∈ K, 0 ≤ ∑ i, y i * z i}

/-- A convex cone: a convex set closed under multiplication by nonnegative scalars. -/
def IsConvexCone {ι : Type*} (K : Set (ι → ℝ)) : Prop :=
  Convex ℝ K ∧ ∀ c : ℝ, 0 ≤ c → ∀ v ∈ K, c • v ∈ K

/-- `V` is the optimal value of a minimization problem whose feasible objective values form `D`,
the minimum being attained whenever the problem is feasible: `V = inf D` (in `EReal`, so `V = +∞`
for an infeasible problem) and, if `D ≠ ∅`, `V = v` for some `v ∈ D`. -/
def IsMinValue (V : EReal) (D : Set ℝ) : Prop :=
  V = sInf ((fun v : ℝ => (v : EReal)) '' D) ∧ (D.Nonempty → ∃ v ∈ D, V = (v : EReal))

end RobustSAA.Discrete.Supplement


