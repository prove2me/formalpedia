-- Prove2me | Definitions.Def_OAI_PiExponent_AdmissibleDeterminantParameters
-- name    : OAI_PiExponent_AdmissibleDeterminantParameters
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-07T19:28:57.27253+00:00
-- url     : https://prove2.me/theorems/658ccfed-c1c8-4674-bbdd-50c0ace16714
-- title:
--   Admissible parameters for the pi determinant construction
-- statement:
--   This is the fixed parameter family used in the determinant construction for a real exponent $\nu$. Its rational parameters $\theta,A,B,C$ and real parameter $\eta$ satisfy the source's order, volume, and exponent-gap conditions. The family also carries a positive tolerance $\epsilon$, an initial scale $F_0$, a dimension $m\ge1$, a multiplicity $K$, positive rational scales $w_0,v_0,\sigma$, and integer numerators and natural denominators with
--
--   $$q_n\ge2,\qquad p_n\ne0,\qquad |\pi-p_n/q_n|\le q_n^{-\nu}.$$
--
--   The weights are $x_0=1$ and $x_{n+1}=\lceil\log q_n\rceil$. Their growth, their minimum $w_*>0$, and the three error budgets satisfy the exact separation and margin conditions of the pinned source. In particular, the three budgets are each less than $\epsilon/3$, while $\epsilon$ is smaller than the exponent gap and at most $1/2$; the collision budget exceeds $2$.
--
--   The arithmetic and analytic errors are the source's functions of this fixed data, with the analytic error split into translation and holomorphic contributions. The arithmetic constant is $\Lambda=\log4+4$. This module retains every field of the original admissible-parameter structure, so later geometric and analytic statements apply to the same family.
--
--   **Formalization Note.** Only source definitions and structures are included. No existence theorem, interpolation theorem, or determinant estimate is asserted by this definition file.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleParameters.lean#L14-L110 ; error definitions L295-L307; Parameters.lean#L93-L110; LocalAlgebra/Dimension.lean#L17-L22; WeightSeparation.lean#L20-L21,L107-L108; Arithmetic.lean#L13

-- Definitions transcribed from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a.
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
noncomputable section
namespace OAI
namespace PiExponentApprox
def weightSeparationFactor (m : ℕ) (C w0 v0 theta : ℝ) : ℝ :=
  C * (max 1 (max v0 (1 / theta) / min w0 1)) ^ (m + 1)

def SeparatedWeightGrowth (m : ℕ) (D : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ i, 0 < i → i ≤ m → D * (∏ j ∈ Finset.range i, x j) < x i

end PiExponentApprox
namespace PiExponent
structure Parameters (ν : ℝ) where
  theta : ℚ
  A : ℚ
  B : ℚ
  C : ℚ
  eta : ℝ
  theta_pos : 0 < (theta : ℝ)
  theta_lt_A : (theta : ℝ) < A
  A_lt_B : (A : ℝ) < B
  B_lt_one : (B : ℝ) < 1
  approximation_gap : 1 - (theta : ℝ) < ν * ((A : ℝ) - theta)
  one_lt_C : 1 < (C : ℝ)
  B_lt_inv_C : (B : ℝ) < 1 / C
  B_lt_C_theta : (B : ℝ) < (C : ℝ) * theta
  C_theta_lt_one : (C : ℝ) * theta < 1
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  gap_pos : 0 < ν * ((A : ℝ) * (1 - eta) - theta) - (1 - theta)

def dimensionK (C : ℝ) (m : ℕ) : ℕ := ⌊C ^ m⌋₊

def dimensionW (B : ℝ) (m : ℕ) : ℝ := (B ^ m)⁻¹

def dimensionV (theta B C : ℝ) (m : ℕ) : ℝ :=
  2 * (dimensionK C m : ℝ) * theta ^ m * dimensionW B m

noncomputable def interpolationSeparationConstant (m : ℕ) (sigma : ℚ) : ℝ :=
  2 * ((m : ℝ) + 2) ^ (m + 2) *
    (1 + ((m : ℝ) + 2) / (sigma : ℝ)) ^ (m + 2)

noncomputable def weightErrorCoefficient (nu theta : ℝ) (K : ℕ) : ℝ :=
  theta + Real.log 4 + Real.log (2 * (K : ℝ)) + nu + Real.log (200 * (K : ℝ))

structure AdmissibleParameters (nu Lambda c : ℝ) where
  base : Parameters nu
  epsilon : ℝ
  F0 : ℝ
  m : ℕ
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  sigma : ℚ
  p : ℕ → ℤ
  q : ℕ → ℕ
  x : ℕ → ℝ
  wstar : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_gap : epsilon <
    nu * ((base.A : ℝ) * (1 - base.eta) - base.theta) - (1 - base.theta)
  epsilon_le_half : epsilon ≤ 1 / 2
  F0_pos : 0 < F0
  F0_large : 2 / (base.theta : ℝ) < F0
  initial_margin : nu / F0 < epsilon / 3
  m_pos : 1 ≤ m
  K_eq : K = dimensionK (base.C : ℝ) m
  K_pos : 1 ≤ K
  w0_eq : (w0 : ℝ) = dimensionW (base.B : ℝ) m
  v0_eq : (v0 : ℝ) = dimensionV (base.theta : ℝ) base.B base.C m
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  volume_eq : (K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m = 1 / 2
  volume_lt_one : (K : ℝ) * (base.theta : ℝ) ^ m < 1
  dimension_margin :
    (Lambda * F0 * (m : ℝ) + 2 * Real.log 2) / (v0 : ℝ) +
      100 * (K : ℝ) / (w0 : ℝ) < epsilon / 3
  collision_margin : 2 < c *
    (base.eta ^ 2 * (K : ℝ) * (base.theta : ℝ) ^ m /
      (((m : ℝ) + 1) * (v0 : ℝ) * (base.A : ℝ) ^ m))
  sigma_pos : 0 < (sigma : ℝ)
  sigma_volume : (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
    ((K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m) < 1
  sigma_centers : (1 + 3 * (sigma : ℝ)) ^ m *
    ((K : ℝ) * (base.theta : ℝ) ^ m) < 1
  sigma_theta : (1 + (sigma : ℝ)) * (base.theta : ℝ) < 1
  x_zero : x 0 = 1
  x_log : ∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)
  approximations : ∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
    |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu)
  x_one_le : ∀ i, 1 ≤ x i
  weight_growth : PiExponentApprox.SeparatedWeightGrowth m
    (PiExponentApprox.weightSeparationFactor m (interpolationSeparationConstant m sigma)
      w0 v0 base.theta) x
  wstar_pos : 0 < wstar
  wstar_lower : ∀ i : Fin m, wstar ≤ x (i.val + 1)
  wstar_attained : ∃ i : Fin m, wstar = x (i.val + 1)
  weight_margin : Lambda * (∑ i : Fin m, 1 / x (i.val + 1)) +
    weightErrorCoefficient nu base.theta K / wstar < epsilon / 3

namespace AdmissibleParameters
variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)

noncomputable def arithmeticError : ℝ :=
  Lambda * d.F0 * (d.m : ℝ) / (d.v0 : ℝ) +
    Lambda * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) + (d.base.theta : ℝ) / d.wstar

noncomputable def translationError : ℝ :=
  nu / d.F0 + Real.log 2 / (d.v0 : ℝ) +
    (Real.log 4 + Real.log (2 * (d.K : ℝ)) + nu) / d.wstar

noncomputable def holomorphicError : ℝ :=
  100 * (d.K : ℝ) / (d.w0 : ℝ) + Real.log 2 / (d.v0 : ℝ) +
    Real.log (200 * (d.K : ℝ)) / d.wstar

noncomputable def analyticError : ℝ := d.translationError + d.holomorphicError

end AdmissibleParameters
namespace Arithmetic
noncomputable def lcmConstant : ℝ := Real.log 4 + 4

end Arithmetic
end PiExponent
end OAI


