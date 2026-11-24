-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_QuadraticFieldSqrtNegSeven
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_QuadraticFieldSqrtNegSeven
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:40.53498+00:00
-- url     : https://prove2.me/theorems/5ca49009-7cf0-4fbb-9f08-e68511449d22
-- title:
--   Quadratic Field Sqrt Neg Seven
-- statement:
--   Definitions and structural lemmas for Quadratic Field Sqrt Neg Seven, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/QuadraticFieldSqrtNegSeven.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Theta
open NumberField
section Statement
def ClassLogPeriodMean.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 16 = 7 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (∃ x : K, x ^ 2 = -(d : K)) →
      ∀ σ : K →+* ℂ,
        (classNumber K : ℝ)⁻¹ * ∑ A : ClassGroup (𝓞 K), classLogPeriod σ A =
          logPeriodConstant d
end Statement
section Ties
instance fact_sevenQ : Fact (∀ r : ℚ, r ^ 2 ≠ -7 + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩
abbrev QuadraticFieldSqrtNegSeven : Type := QuadraticAlgebra ℚ (-7) 0
instance : Algebra.IsQuadraticExtension ℚ QuadraticFieldSqrtNegSeven :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩
instance : NumberField QuadraticFieldSqrtNegSeven where
end Ties
end GroundTheory.Heights₂.Theta


