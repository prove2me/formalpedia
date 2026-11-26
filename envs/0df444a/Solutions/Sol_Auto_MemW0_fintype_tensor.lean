-- Prove2me | solution 1 for Auto.MemW0.fintype_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:59.933836+00:00
-- url     : https://prove2.me/submissions/ff335601-8666-4db7-9af5-948bf28cc983

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_continuous_fintype_tensor
public import Theorems.Thm_Auto_aux_wienerEnvelope_fintype_tensor_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {ι : Type*} [Fintype ι]
    {d : ι → ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, MemW0 (f i)) :
    MemW0 (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (x i)) := by
  classical
  have hcont : Continuous (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦
      ∏ i, f i (x i)) :=
    aux_continuous_fintype_tensor fun i ↦ (hf i).1
  refine ⟨hcont, ?_⟩
  have hprod : Integrable (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦
      ∏ i, wienerEnvelope (f i) 1 (x i)) := by
    exact Integrable.fintype_prod_dep fun i ↦ (hf i).2
  refine hprod.mono_nonneg (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg hcont zero_le_one x)
    (ae_of_all _ fun x ↦ ?_)
  exact aux_wienerEnvelope_fintype_tensor_le (fun i ↦ (hf i).1) x
end MemW0
end Auto
