-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralCompContinuousLinearEquiv
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralCompContinuousLinearEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:05.781103+00:00
-- url     : https://prove2.me/theorems/d2ff8712-2d08-4079-b629-fb399f86cbbf
-- title:
--   Integral Comp Continuous Linear Equiv
-- statement:
--   Definitions and structural lemmas for Integral Comp Continuous Linear Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralCompContinuousLinearEquiv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Yzb9.SelfDual :
    {V : Type} →
      [AddCommGroup V] → [TopologicalSpace V] → [inst : MeasurableSpace V] → MeasureTheory.Measure V → (V → V → ℂ) → Prop :=
    fun {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : MeasureTheory.Measure V) (χ : V → V → ℂ) ↦
      μ.IsAddHaarMeasure ∧
        ∀ (Φ : V → ℂ),
          Continuous Φ →
            HasCompactSupport Φ →
              MeasureTheory.Integrable (fun (y : V) ↦ ∫ (x : V), Φ x * χ x y ∂μ) μ →
                ∀ (z : V), ∫ (y : V), (∫ (x : V), Φ x * χ x y ∂μ) * χ y z ∂μ = Φ (-z)
section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end
section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace NNReal
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end


