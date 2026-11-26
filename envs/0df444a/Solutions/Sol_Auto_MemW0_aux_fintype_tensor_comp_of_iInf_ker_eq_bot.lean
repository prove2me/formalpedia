-- Prove2me | solution 1 for Auto.MemW0.aux_fintype_tensor_comp_of_iInf_ker_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:38.12723+00:00
-- url     : https://prove2.me/submissions/683c2cc2-ab0c-4517-9fe7-b964f5990ec9

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_fintype_tensor_comp_injective
public import Theorems.Thm_Auto_aux_continuousLinearMap_pi_injective_of_iInf_ker_eq_bot

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution
    {ι : Type*} [Fintype ι] {m l : ℕ} {d : ι → ℕ}
    {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, MemW0 (f i))
    (π : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hker : ⨅ i, LinearMap.ker (π i).toLinearMap = ⊥) :
    MemW0 (fun uv : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) ↦
      ∏ i, f i (π i uv)) :=
  MemW0.aux_fintype_tensor_comp_injective hf π
    (aux_continuousLinearMap_pi_injective_of_iInf_ker_eq_bot π hker)
end MemW0
end Auto
