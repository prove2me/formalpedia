-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:00.279303+00:00
-- url     : https://prove2.me/theorems/8cef66ad-4f6c-405e-96fb-b5e3d9a369f9
-- title:
--   Integral Mul Conj Gaussian Eq Coeff Norm Sq
-- statement:
--   Definitions and structural lemmas for Integral Mul Conj Gaussian Eq Coeff Norm Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/IntegralMulConjGaussianEqCoeffNormSq.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
noncomputable def fa1M {g : ℕ} (α : Fin g →₀ ℕ) : ℝ :=
  (Real.pi ^ g)⁻¹ * ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
noncomputable def fa1K {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) : ℝ :=
  ∑ α ∈ p.support, ‖monomialOfMultiindex α z‖ ^ 2 / fa1M α
noncomputable def fa1N {g : ℕ} (p : MvPolynomial (Fin g) ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖MvPolynomial.coeff α p‖ ^ 2 * fa1M α
end ReciprocityTheory.ChartRestriction.G.I2


