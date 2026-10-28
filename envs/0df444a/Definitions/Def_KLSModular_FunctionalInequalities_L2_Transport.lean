-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_L2_Transport
-- name    : KLSModular_FunctionalInequalities_L2_Transport
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:22:24.356978+00:00
-- url     : https://prove2.me/theorems/18833b5b-77e3-4a08-986b-55e8c2b513b7
-- title:
--   L² pullbacks under translations and linear equivalences
-- statement:
--   `L2.Translation.pullback` and `pullbackInv` compose $L^2$ classes with a translation and its inverse, while the corresponding `ContinuousLinearEquiv` definitions do the same for a continuous linear equivalence and its inverse. The inverse identities are proved, and each pair is packaged as a linear isometric equivalence `pullbackEquiv` between the $L^2$ spaces of the source and image probability measures.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Transport
--   import FunctionalInequalities.L2.MeanVariance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def pullback : Lp ℝ 2 (Probability.translateLaw ν c : Measure V) →ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V) :=
--     Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ c + x) (Probability.measurePreserving_translate ν c)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/Transport.lean) · `FunctionalInequalities.L2.Transport` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/Transport.lean#L26-L244 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.Transport`, definition bundle `KLSModular_FunctionalInequalities_L2_Transport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
namespace FunctionalInequalities
namespace L2
universe u v
namespace Translation
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (ν : ProbabilityMeasure V) (c : V)
/-- Pullback of `L²` classes along the translation. -/
def pullback : Lp ℝ 2 (Probability.translateLaw ν c : Measure V) →ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ c + x) (Probability.measurePreserving_translate ν c)
/-- Pullback of `L²` classes along the inverse translation. -/
def pullbackInv : Lp ℝ 2 (ν : Measure V) →ₗᵢ[ℝ] Lp ℝ 2 (Probability.translateLaw ν c : Measure V) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ -c + x) (Probability.measurePreserving_translate_symm ν c)
omit [InnerProductSpace ℝ V] in
theorem pullbackInv_pullback (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    pullbackInv ν c (pullback ν c f) = f := by
  change Lp.compMeasurePreserving (fun x ↦ -c + x) (Probability.measurePreserving_translate_symm ν c)
    (Lp.compMeasurePreserving (fun x ↦ c + x) (Probability.measurePreserving_translate ν c) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (Probability.measurePreserving_translate ν c)
    (Probability.measurePreserving_translate_symm ν c)]
  apply Subtype.ext
  change f.1.compMeasurePreserving ((fun x ↦ c + x) ∘ fun x ↦ -c + x)
    ((Probability.measurePreserving_translate ν c).comp (Probability.measurePreserving_translate_symm ν c)) = f.1
  have hae : ((fun x ↦ c + x) ∘ fun x ↦ -c + x) =ᵐ[(Probability.translateLaw ν c : Measure V)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1
omit [InnerProductSpace ℝ V] in
theorem pullback_pullbackInv (f : Lp ℝ 2 (ν : Measure V)) :
    pullback ν c (pullbackInv ν c f) = f := by
  change Lp.compMeasurePreserving (fun x ↦ c + x) (Probability.measurePreserving_translate ν c)
    (Lp.compMeasurePreserving (fun x ↦ -c + x) (Probability.measurePreserving_translate_symm ν c) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (Probability.measurePreserving_translate_symm ν c)
    (Probability.measurePreserving_translate ν c)]
  apply Subtype.ext
  change f.1.compMeasurePreserving ((fun x ↦ -c + x) ∘ fun x ↦ c + x)
    ((Probability.measurePreserving_translate_symm ν c).comp (Probability.measurePreserving_translate ν c)) = f.1
  have hae : ((fun x ↦ -c + x) ∘ fun x ↦ c + x) =ᵐ[(ν : Measure V)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1
/-- Pullback along the translation as a linear isometric equivalence of real `L²` spaces. -/
def pullbackEquiv : Lp ℝ 2 (Probability.translateLaw ν c : Measure V) ≃ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V) where
  toFun := pullback ν c
  invFun := pullbackInv ν c
  left_inv := pullbackInv_pullback ν c
  right_inv := pullback_pullbackInv ν c
  map_add' := map_add (pullback ν c)
  map_smul' := map_smul (pullback ν c)
  norm_map' := norm_map (pullback ν c)
omit [InnerProductSpace ℝ V] in
@[simp]
theorem pullbackEquiv_apply (f : Lp ℝ 2 (Probability.translateLaw ν c : Measure V)) :
    pullbackEquiv ν c f = pullback ν c f := rfl
omit [InnerProductSpace ℝ V] in
@[simp]
theorem pullbackEquiv_symm_apply (f : Lp ℝ 2 (ν : Measure V)) :
    (pullbackEquiv ν c).symm f = pullbackInv ν c f := rfl
end Translation
namespace ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
/-- Pullback of `L²` classes along `T`. -/
def pullback : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) →ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V₁) :=
  Lp.compMeasurePreservingₗᵢ ℝ T (Probability.measurePreserving_mapContinuousLinearEquiv ν T)
/-- Pullback of `L²` classes along `T⁻¹`. -/
def pullbackInv : Lp ℝ 2 (ν : Measure V₁) →ₗᵢ[ℝ] Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) :=
  Lp.compMeasurePreservingₗᵢ ℝ T.symm (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)
theorem pullbackInv_pullback (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    pullbackInv ν T (pullback ν T f) = f := by
  change Lp.compMeasurePreserving T.symm (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)
    (Lp.compMeasurePreserving T (Probability.measurePreserving_mapContinuousLinearEquiv ν T) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (Probability.measurePreserving_mapContinuousLinearEquiv ν T)
    (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)]
  apply Subtype.ext
  change f.1.compMeasurePreserving (⇑T ∘ ⇑T.symm)
    ((Probability.measurePreserving_mapContinuousLinearEquiv ν T).comp (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)) = f.1
  have hae : (⇑T ∘ ⇑T.symm) =ᵐ[(Probability.mapContinuousLinearEquiv ν T : Measure V₂)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1
theorem pullback_pullbackInv (f : Lp ℝ 2 (ν : Measure V₁)) :
    pullback ν T (pullbackInv ν T f) = f := by
  change Lp.compMeasurePreserving T (Probability.measurePreserving_mapContinuousLinearEquiv ν T)
    (Lp.compMeasurePreserving T.symm (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T)
    (Probability.measurePreserving_mapContinuousLinearEquiv ν T)]
  apply Subtype.ext
  change f.1.compMeasurePreserving (⇑T.symm ∘ ⇑T)
    ((Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T).comp (Probability.measurePreserving_mapContinuousLinearEquiv ν T)) = f.1
  have hae : (⇑T.symm ∘ ⇑T) =ᵐ[(ν : Measure V₁)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1
/-- Pullback along `T` as a linear isometric equivalence of real `L²` spaces. -/
def pullbackEquiv : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂) ≃ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V₁) where
  toFun := pullback ν T
  invFun := pullbackInv ν T
  left_inv := pullbackInv_pullback ν T
  right_inv := pullback_pullbackInv ν T
  map_add' := map_add (pullback ν T)
  map_smul' := map_smul (pullback ν T)
  norm_map' := norm_map (pullback ν T)
@[simp]
theorem pullbackEquiv_apply (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    pullbackEquiv ν T f = pullback ν T f := rfl
@[simp]
theorem pullbackEquiv_symm_apply (f : Lp ℝ 2 (ν : Measure V₁)) :
    (pullbackEquiv ν T).symm f = pullbackInv ν T f := rfl
end ContinuousLinearEquiv
end L2
end FunctionalInequalities


