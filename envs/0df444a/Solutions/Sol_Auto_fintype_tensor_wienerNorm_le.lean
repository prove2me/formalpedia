-- Prove2me | solution 1 for Auto.fintype_tensor_wienerNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:59.340035+00:00
-- url     : https://prove2.me/submissions/0b32fdd5-d88d-4fb5-a4e9-145a5c35c600

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_wienerEnvelope_fintype_tensor_le
public import Theorems.Thm_Auto_MemW0_fintype_tensor

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {ι : Type*} [Fintype ι]
    {d : ι → ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, MemW0 (f i)) :
    (∫ x : ∀ i, EuclideanSpace ℝ (Fin (d i)),
      wienerEnvelope (fun y : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (y i)) 1 x) ≤
      ∏ i, ∫ x, wienerEnvelope (f i) 1 x := by
  classical
  have hTensor := MemW0.fintype_tensor hf
  have hprod : Integrable (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦
      ∏ i, wienerEnvelope (f i) 1 (x i)) := by
    exact Integrable.fintype_prod_dep fun i ↦ (hf i).2
  calc
    (∫ x : ∀ i, EuclideanSpace ℝ (Fin (d i)),
      wienerEnvelope (fun y : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (y i)) 1 x) ≤
        ∫ x : ∀ i, EuclideanSpace ℝ (Fin (d i)), ∏ i, wienerEnvelope (f i) 1 (x i) :=
      integral_mono hTensor.2 hprod
        (fun x ↦ aux_wienerEnvelope_fintype_tensor_le (fun i ↦ (hf i).1) x)
    _ = ∏ i, ∫ x, wienerEnvelope (f i) 1 x :=
      integral_fintype_prod_volume_eq_prod (fun i ↦ wienerEnvelope (f i) 1)
end Auto
