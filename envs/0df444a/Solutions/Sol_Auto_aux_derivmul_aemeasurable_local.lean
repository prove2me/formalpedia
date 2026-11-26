-- Prove2me | solution 1 for Auto.aux_derivmul_aemeasurable_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:35.733517+00:00
-- url     : https://prove2.me/submissions/c0ca5139-398b-45c2-8117-64a8206559ef

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
public import Theorems.Thm_Auto_aux_deriv_eq_derivWithin_ae

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {α β x y : ℝ} (hαβ : α < β)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    AEMeasurable (fun t ↦ ‖t * deriv a t‖ₑ)
      ((aux_logarithmicMeasure α β).restrict (Set.Icc x y)) := by
  have hcont : ContinuousOn (id * derivWithin a (Set.Icc α β)) (Set.Icc α β) :=
    continuousOn_id.mul (ha.continuousOn_derivWithin (uniqueDiffOn_Icc hαβ) (by norm_num))
  have hcontLocal : ContinuousOn (id * derivWithin a (Set.Icc α β)) (Set.Icc x y) :=
    hcont.mono (Icc_subset_Icc hx.1 hy.2)
  have hwithin_meas0 : AEMeasurable (id * derivWithin a (Set.Icc α β))
      ((aux_logarithmicMeasure α β).restrict (Set.Icc x y)) :=
    hcontLocal.aemeasurable measurableSet_Icc
  have hwithin_meas : AEMeasurable (fun t ↦ ‖t * derivWithin a (Set.Icc α β) t‖ₑ)
      ((aux_logarithmicMeasure α β).restrict (Set.Icc x y)) := by
    simpa only [Pi.mul_apply, id_eq] using hwithin_meas0.enorm
  apply hwithin_meas.congr
  filter_upwards [(aux_deriv_eq_derivWithin_ae (α := α) (β := β) a).restrict] with t ht
  simp only [ht]
end Auto
