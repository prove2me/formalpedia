-- Prove2me | Definitions.Def_BirkhoffGlobalSection_EHCriticalConvexity
-- name    : BirkhoffGlobalSection_EHCriticalConvexity
-- status  : Definition
-- author  : @Sneed
-- created : 2026-09-30T05:48:23.277161+00:00
-- url     : https://prove2.me/theorems/03649388-feef-425b-b18b-43c264777593
-- title:
--   Elliptic-hyperbolic critical data at $\\mu=1/2$, $h=-2$
-- statement:
--   Explicit elliptic-hyperbolic data for the strict convexity of the equal-mass critical surface.
--
--   At mass ratio $\\mu=1/2$ and energy $h=-2$, the Liu--Salomao regularization of Section 9.2 writes the Hamiltonian as
--
--   $$
--   \\hat{H}(y,x)=\\frac{(y_1+f_1(x))^2+(y_2+f_2(x))^2}{2}+V(x),
--   $$
--
--   with decoupled magnetic field $F=(f_1,f_2)=\\frac{1}{8}(\\sin 2x_2,\\sinh 2x_1)$ and potential $V(x)=W_1(x_1)+W_2(x_2)$, where
--
--   $$
--   W_1(x_1)=\\frac{\\cosh^2 x_1}{2}-\\frac{\\cosh x_1}{2}-\\frac{\\sinh^2 2x_1}{128},\\qquad W_2(x_2)=-\\frac{\\cos^2 x_2}{2}-\\frac{\\sin^2 2x_2}{128}.
--   $$
--
--   This file records these functions as `ehF1`, `ehF2`, `ehW1`, `ehW2`, `ehV` and the model Hamiltonian `ehCriticalHamiltonian` on model `Phase` coordinates $![y_1,y_2,x_1,x_2]$, together with the reduced determinant coefficients `ehCt`, `ehDs` and `ehDetUW` of equation (9.11) and the first-quadrant estimate region `ehEstimateRegion` where Theorem 9.4 applies.
--
--   These data pin down the reference model used by the critical convexity theorems, so that the construction (Section 9.2) and the estimates (Theorems 9.1 and 9.4) can be formalized as separate problems sharing one faithful reference.
--
--   **Formalization Note** Momenta are `y 0, y 1` and positions `y 2, y 3`. Derivatives inside `ehCt`, `ehDs`, `ehDetUW` use Mathlib `deriv`, so the stated coefficients are correct by construction from `ehF1`, `ehF2`, `ehW1`, `ehW2`.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2, Section 9.2 (elliptic-hyperbolic regularization) and Section 9.3 (explicit F and V at mu = 1/2, Theorem 9.4, eq. 9.11).

import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace BirkhoffGlobalSection

noncomputable section

/-- Liu--Salomao §9.2, magnetic component `f₁(x₂) = sin(2x₂)/8` at `μ = 1/2`. -/
def ehF1 (x2 : ℝ) : ℝ := Real.sin (2 * x2) / 8

/-- Liu--Salomao §9.2, magnetic component `f₂(x₁) = sinh(2x₁)/8` at `μ = 1/2`. -/
def ehF2 (x1 : ℝ) : ℝ := Real.sinh (2 * x1) / 8

/-- Liu--Salomao §9.3, first potential factor at the critical energy `h = -2`:
`W₁(x₁) = cosh²x₁/2 - cosh x₁/2 - sinh²(2x₁)/128`. -/
def ehW1 (x1 : ℝ) : ℝ :=
  Real.cosh x1 ^ 2 / 2 - Real.cosh x1 / 2 - Real.sinh (2 * x1) ^ 2 / 128

/-- Liu--Salomao §9.3, second potential factor at `h = -2`:
`W₂(x₂) = -cos²x₂/2 - sin²(2x₂)/128`. -/
def ehW2 (x2 : ℝ) : ℝ :=
  -Real.cos x2 ^ 2 / 2 - Real.sin (2 * x2) ^ 2 / 128

/-- Liu--Salomao §9.3, decoupled critical potential `V = W₁ + W₂`. -/
def ehV (x1 x2 : ℝ) : ℝ := ehW1 x1 + ehW2 x2

/-- Liu--Salomao §9.2, regularized Hamiltonian at `μ = 1/2`, `h = -2`,
on model `Phase` coordinates `![y₁,y₂,x₁,x₂]`:
`Ĥ = ½((y₁+f₁)² + (y₂+f₂)²) + V`. -/
def ehCriticalHamiltonian (y : Phase) : ℝ :=
  ((y 0 + ehF1 (y 3)) ^ 2 + (y 1 + ehF2 (y 2)) ^ 2) / 2 + ehV (y 2) (y 3)

/-- Squared momentum radius `r² = 2(h-V)` at the zero level (Thm 9.1). -/
def ehR2 (x1 x2 : ℝ) : ℝ := -2 * ehV x1 x2

/-- §9.3 reduced coefficient `c_t` at `(s,t) = (cos θ, sin θ)` (eq. 9.11):
`c_t = r·t·f₂,₁₁ + V₁₁`. -/
def ehCt (t x1 x2 : ℝ) : ℝ :=
  Real.sqrt (ehR2 x1 x2) * t * deriv (deriv ehF2) x1 + deriv (deriv ehW1) x1

/-- §9.3 reduced coefficient `d_s` (eq. 9.11): `d_s = r·s·f₁,₂₂ + V₂₂`. -/
def ehDs (s x1 x2 : ℝ) : ℝ :=
  Real.sqrt (ehR2 x1 x2) * s * deriv (deriv ehF1) x2 + deriv (deriv ehW2) x2

/-- §9.3 determinant (eq. 9.11, Cor 9.3(ii)):
`det U_W = d_s·(V₁² + r²·c_t) + c_t·V₂²`. -/
def ehDetUW (s t x1 x2 : ℝ) : ℝ :=
  ehDs s x1 x2 * (deriv ehW1 x1 ^ 2 + ehR2 x1 x2 * ehCt t x1 x2) +
    ehCt t x1 x2 * deriv ehW2 x2 ^ 2

/-- Liu--Salomao §9.3, first-quadrant estimate region `ℋ₁` minus the
singularity, at the critical level: Hill condition `V ≤ 0`, regularity of
the level, and angle-uniform positivity of `det U_W` (Thm 9.4(i)). -/
def ehEstimateRegion : Set Phase :=
  {y | 0 ≤ y 2 ∧ 0 ≤ y 3 ∧ y 3 ≤ Real.pi / 2 ∧ ehV (y 2) (y 3) ≤ 0 ∧
    (y 2 ≠ 0 ∨ y 3 ≠ Real.pi / 2) ∧
    ehCriticalHamiltonian y = 0 ∧ fderiv ℝ ehCriticalHamiltonian y ≠ 0 ∧
    ∀ s t : ℝ, s ^ 2 + t ^ 2 = 1 → 0 < ehDetUW s t (y 2) (y 3)}

end

end BirkhoffGlobalSection


