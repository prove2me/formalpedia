-- Prove2me | Definitions.Def_ExpConeIPM_Curvature_ExpCone
-- name    : ExpConeIPM_Curvature_ExpCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:29.819979+00:00
-- url     : https://prove2.me/theorems/f58adc5f-e58b-4344-9a38-0cf13afdc8ef
-- title:
--   The exponential cone $K_{\exp}$, its barrier (2) and the functions $\psi$, $g$, $h$ of Appendix A.1
-- statement:
--   Write $x = (x_1, x_2, x_3)$ for a point of $\mathbb{R}^3$. The **exponential cone** is the closure
--
--   $$
--   K_{\exp} = \operatorname{cl}\{x \in \mathbb{R}^3 \mid x_1 \ge x_2 \exp(x_3/x_2),\ x_2 > 0\},
--   $$
--
--   and its standard logarithmic **barrier** is
--
--   $$
--   F(x) = -\log\bigl(x_2 \log(x_1/x_2) - x_3\bigr) - \log x_1 - \log x_2. \qquad (2)
--   $$
--
--   Appendix A.1 splits the barrier through the auxiliary functions
--
--   $$
--   \psi(x) = x_2 \log(x_1/x_2) - x_3, \qquad g(x) = -\log \psi(x), \qquad h(x) = -\log x_1 - \log x_2,
--   $$
--
--   so that $F = g + h$. On the interior of the cone, $x_1 > 0$, $x_2 > 0$ and $\psi(x) > 0$, so $F$ is smooth there.
--
--   These are the objects of Dahl and Andersen's interior-point method for exponential-cone optimization; the exponential cone models entropy, logarithm and exponential constraints, and its barrier is the function whose derivatives the algorithm evaluates.
--
--   **Formalization Note** Points of $\mathbb{R}^3$ are `EuclideanSpace ℝ (Fin 3)`; the paper's $(x_1, x_2, x_3)$ are `(x 0, x 1, x 2)`. The cone is defined as the closure of the printed set, not by its interior. $F$, $\psi$, $g$, $h$ are defined on all of $\mathbb{R}^3$ by their formulas with `Real.log`, which returns junk values at non-positive arguments; every statement of the mission uses them, and their derivatives (which are local), only at points of the interior of $K_{\exp}$, where every logarithm is the genuine one. The claim that $F$ is a 3-self-concordant barrier (quoted from Chares) is not part of this definition.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 346, (2), and p. 367, Appendix A.1

import Mathlib

namespace ExpConeIPM.Curvature

/-!
# The exponential cone and its barrier (Dahl–Andersen 2022, §2, p. 346, and A.1, p. 367)

Dahl, Andersen, *A primal-dual interior-point algorithm for nonsymmetric exponential-cone
optimization*, Math. Program. 194 (2022), p. 346, (2), and p. 367, Appendix A.1.

Index convention: the paper's coordinates `(x₁, x₂, x₃)` of `x ∈ ℝ³` are `(x 0, x 1, x 2)` here.

The barrier is defined on all of `ℝ³` by the formula (2), with `Real.log`. `Real.log` returns junk
values on non-positive arguments, but every statement of this development evaluates the barrier (or
its derivatives, which are local) only at points of `int(Kexp)`, where `x₁ > 0`, `x₂ > 0` and
`ψ(x) > 0`, so all logarithms there are the genuine ones.
-/

/-- **The exponential cone** (§2, p. 346):
`Kexp = cl{x ∈ ℝ³ | x₁ ≥ x₂ exp(x₃/x₂), x₂ > 0}`, the closure of the set as printed. -/
def Kexp : Set (EuclideanSpace ℝ (Fin 3)) :=
  closure {x | x 0 ≥ x 1 * Real.exp (x 2 / x 1) ∧ x 1 > 0}

/-- `ψ(x) = x₂ log(x₁/x₂) − x₃` (A.1, p. 367). -/
noncomputable def psi (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  x 1 * Real.log (x 0 / x 1) - x 2

/-- `g(x) = −log(ψ(x))` (A.1, p. 367). -/
noncomputable def g (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  -Real.log (psi x)

/-- `h(x) = −log x₁ − log x₂` (A.1, p. 367). -/
noncomputable def h (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  -Real.log (x 0) - Real.log (x 1)

/-- **The exponential-cone barrier** (2), p. 346:
`F(x) = −log(x₂ log(x₁/x₂) − x₃) − log x₁ − log x₂`. -/
noncomputable def barrier (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  -Real.log (x 1 * Real.log (x 0 / x 1) - x 2) - Real.log (x 0) - Real.log (x 1)

end ExpConeIPM.Curvature


