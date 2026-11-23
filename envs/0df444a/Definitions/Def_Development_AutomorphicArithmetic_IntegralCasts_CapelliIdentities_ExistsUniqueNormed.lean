-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueNormed
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueNormed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:11.668703+00:00
-- url     : https://prove2.me/theorems/2e20a083-b761-4180-b22a-76d194ac8970
-- title:
--   Exists Unique Normed
-- statement:
--   Definitions and structural lemmas for Exists Unique Normed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsUniqueNormed.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Yzb8.SelfDual :
    {V : Type} →
      [AddCommGroup V] → [TopologicalSpace V] → [inst : MeasurableSpace V] → MeasureTheory.Measure V → (V → V → ℂ) → Prop :=
    fun {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : MeasureTheory.Measure V) (χ : V → V → ℂ) ↦
      μ.IsAddHaarMeasure ∧
        ∀ (Φ : V → ℂ),
          Continuous Φ →
            HasCompactSupport Φ →
              MeasureTheory.Integrable (fun (y : V) ↦ ∫ (x : V), Φ x * χ x y ∂μ) μ →
                ∀ (z : V), ∫ (y : V), (∫ (x : V), Φ x * χ x y ∂μ) * χ y z ∂μ = Φ (-z)
namespace UpperTheory.Reformulated.B.Yzb8
open MeasureTheory FourierTransform
open scoped NNReal ENNReal
section aux
variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
noncomputable def ee (t : ℝ) : ℂ :=
  Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ))
end aux
end UpperTheory.Reformulated.B.Yzb8
open MeasureTheory FourierTransform UpperTheory.Reformulated.B.Yzb8
open scoped NNReal ENNReal


