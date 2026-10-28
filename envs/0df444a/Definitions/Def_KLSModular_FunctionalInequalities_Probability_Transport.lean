-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
-- name    : KLSModular_FunctionalInequalities_Probability_Transport
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:16:57.149003+00:00
-- url     : https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564
-- title:
--   Probability-law transport by affine and linear equivalences
-- statement:
--   `Probability.translateLaw ν c` is the pushforward of a probability law $\nu$ under $x\mapsto c+x$, and `Probability.mapLinearIsometryEquiv` and `Probability.mapContinuousLinearEquiv` are the pushforwards under the indicated linear isometric or continuous linear equivalences. The declarations `measurePreserving_translate`, `measurePreserving_translate_symm`, `measurePreserving_mapContinuousLinearEquiv`, and `measurePreserving_mapContinuousLinearEquiv_symm` state that each map preserves measure in the forward direction and that the corresponding inverse map recovers the original law. The coercion lemmas identify these bundled probability laws with the relevant measure pushforwards.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Covariance.Basic
--   import FunctionalInequalities.Probability.AffineSupport
--   import Mathlib.Analysis.InnerProductSpace.Adjoint
--   import Mathlib.MeasureTheory.Measure.Tilted
--   import Mathlib.MeasureTheory.Measure.Support
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def Probability.translateLaw : ProbabilityMeasure V :=
--     ν.map (measurable_const_add c).aemeasurable
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   Theorems in source order:
--
--   - [`Probability.tilted_smul_pos`](https://prove2.me/theorems/082bb7e7-9916-4a6e-aaa8-68ce8d9f378f)
--   - [`Covariance.operator_map_continuousLinearEquiv`](https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329)
--   - [`Probability.affineSupport_mapContinuousLinearEquiv`](https://prove2.me/theorems/fde395de-3098-465b-b70c-cf883c0311a9)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Transport.lean) · `FunctionalInequalities.Probability.Transport` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Transport.lean#L129-L289 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Transport`, definition bundle `KLSModular_FunctionalInequalities_Probability_Transport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
namespace FunctionalInequalities
universe u v
section Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : ProbabilityMeasure V) (c : V)
/-- The image of `ν` under the translation `x ↦ c + x`. -/
def Probability.translateLaw : ProbabilityMeasure V :=
  ν.map (measurable_const_add c).aemeasurable
omit [InnerProductSpace ℝ V] in
theorem Probability.coe_translateLaw :
    (Probability.translateLaw ν c : Measure V) = (ν : Measure V).map (fun x ↦ c + x) := rfl
omit [InnerProductSpace ℝ V] in
/-- The translation is measure preserving from `ν` to the translated law. -/
theorem Probability.measurePreserving_translate :
    MeasurePreserving (fun x ↦ c + x) (ν : Measure V) (Probability.translateLaw ν c : Measure V) :=
  ⟨measurable_const_add c, rfl⟩
omit [InnerProductSpace ℝ V] in
/-- The inverse translation is measure preserving from the translated law back to `ν`. -/
theorem Probability.measurePreserving_translate_symm :
    MeasurePreserving (fun x ↦ -c + x) (Probability.translateLaw ν c : Measure V) (ν : Measure V) := by
  refine ⟨measurable_const_add _, ?_⟩
  rw [Probability.coe_translateLaw, Measure.map_map (measurable_const_add _) (measurable_const_add _)]
  have : ((fun x ↦ -c + x) ∘ fun x ↦ c + x) = id := by
    funext x
    simp
  rw [this, Measure.map_id]
variable [CompleteSpace V]
end Translation
section LinearIsometry
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (L : V₁ ≃ₗᵢ[ℝ] V₂)
/-- The image of `ν` under the linear isometric equivalence `L`. -/
def Probability.mapLinearIsometryEquiv : ProbabilityMeasure V₂ :=
  ν.map L.continuous.measurable.aemeasurable
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
end LinearIsometry
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
/-- The image of `ν` under the continuous linear equivalence `T`. -/
def Probability.mapContinuousLinearEquiv : ProbabilityMeasure V₂ :=
  ν.map T.continuous.measurable.aemeasurable
theorem Probability.coe_mapContinuousLinearEquiv : (Probability.mapContinuousLinearEquiv ν T : Measure V₂) = (ν : Measure V₁).map T := rfl
/-- `T` is measure preserving from `ν` to its image law. -/
theorem Probability.measurePreserving_mapContinuousLinearEquiv :
    MeasurePreserving T (ν : Measure V₁) (Probability.mapContinuousLinearEquiv ν T : Measure V₂) :=
  ⟨T.continuous.measurable, rfl⟩
/-- `T⁻¹` is measure preserving from the image law back to `ν`. -/
theorem Probability.measurePreserving_mapContinuousLinearEquiv_symm :
    MeasurePreserving T.symm (Probability.mapContinuousLinearEquiv ν T : Measure V₂) (ν : Measure V₁) := by
  refine ⟨T.symm.continuous.measurable, ?_⟩
  rw [Probability.coe_mapContinuousLinearEquiv, Measure.map_map T.symm.continuous.measurable T.continuous.measurable]
  have : (⇑T.symm ∘ ⇑T) = id := by
    funext x
    simp
  rw [this, Measure.map_id]
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
end ContinuousLinearEquiv
end FunctionalInequalities


