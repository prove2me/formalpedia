-- Prove2me | solution 1 for Auto.aux_memW0_finAdd_tensor_of_memW0_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:48.605439+00:00
-- url     : https://prove2.me/submissions/9f167d56-01b1-44b6-8798-51cdb086d819

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_finAdd_measurePreserving
public import Theorems.Thm_Auto_aux_wienerEnvelope_finAdd_tensor_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {n m : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} {g : EuclideanSpace ℝ (Fin m) → 𝕜}
    (hf : Continuous f) (hg : Continuous g)
    (hprod : MemW0 (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
      f p.1 * g p.2)) :
    MemW0 (fun z : EuclideanSpace ℝ (Fin (n + m)) ↦
      f (EuclideanSpace.finAddEquivProd z).1 * g (EuclideanSpace.finAddEquivProd z).2) := by
  let e : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  let H : EuclideanSpace ℝ (Fin (n + m)) → 𝕜 := fun z ↦ f (e z).1 * g (e z).2
  let P : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → 𝕜 := fun p ↦ f p.1 * g p.2
  have hH : Continuous H := (hf.comp (e.continuous.fst)).mul (hg.comp (e.continuous.snd))
  have hP : Continuous P := (hf.comp continuous_fst).mul (hg.comp continuous_snd)
  change MemW0 H
  refine ⟨hH, ?_⟩
  have hcomp : Integrable (wienerEnvelope P 1 ∘ e) :=
    (aux_finAdd_measurePreserving n m).integrable_comp_emb
      e.toHomeomorph.measurableEmbedding |>.mpr hprod.2
  refine hcomp.mono_nonneg (continuous_wienerEnvelope hH 1).aestronglyMeasurable
    (ae_of_all _ fun z ↦ aux_wienerEnvelope_nonneg hH zero_le_one z) (ae_of_all _ fun z ↦ ?_)
  exact aux_wienerEnvelope_finAdd_tensor_le hf hg z
end Auto
