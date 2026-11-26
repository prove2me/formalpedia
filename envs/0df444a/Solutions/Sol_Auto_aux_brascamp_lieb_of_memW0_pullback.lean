-- Prove2me | solution 1 for Auto.aux_brascamp_lieb_of_memW0_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:46.412847+00:00
-- url     : https://prove2.me/submissions/c6e8e92a-4979-4ff8-8f7c-537dee57bce1

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice
public import Theorems.Thm_Auto_MemW0_aux_integral_slice
public import Theorems.Thm_Auto_aux_integral_wienerEnvelope_integral_slice_le
public import Theorems.Thm_Auto_MemW0_fintype_tensor
public import Theorems.Thm_Auto_fintype_tensor_wienerNorm_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {ι : Type*} [Fintype ι] {m l : ℕ} {d : ι → ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜]
    (f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜) (hf : ∀ i, MemW0 (f i))
    (pi : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hPullback : MemW0 (fun uv : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) ↦
      ∏ i, f i (pi i uv)))
    {C : ℝ} (hC : 0 ≤ C)
    (hPullback_bound :
      (∫ uv : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l),
        wienerEnvelope (fun uv ↦ ∏ i, f i (pi i uv)) 1 uv) ≤
        C * ∫ x : ∀ i, EuclideanSpace ℝ (Fin (d i)),
          wienerEnvelope (fun y ↦ ∏ i, f i (y i)) 1 x) :
    MemW0 (fun x : ∀ i, EuclideanSpace ℝ (Fin (d i)) ↦ ∏ i, f i (x i)) ∧
      (∀ u : EuclideanSpace ℝ (Fin m),
        MemW0 (fun v : EuclideanSpace ℝ (Fin l) ↦ ∏ i, f i (pi i (u, v)))) ∧
      MemW0 (fun u : EuclideanSpace ℝ (Fin m) ↦ ∫ v, ∏ i, f i (pi i (u, v))) ∧
      (∫ u : EuclideanSpace ℝ (Fin m),
        wienerEnvelope (fun u ↦ ∫ v, ∏ i, f i (pi i (u, v))) 1 u) ≤
        C * ∏ i, ∫ x, wienerEnvelope (f i) 1 x := by
  classical
  let H : (∀ i, EuclideanSpace ℝ (Fin (d i))) → 𝕜 := fun x ↦ ∏ i, f i (x i)
  let P : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜 :=
    fun uv ↦ ∏ i, f i (pi i uv)
  let G : EuclideanSpace ℝ (Fin m) → 𝕜 := fun u ↦ ∫ v, ∏ i, f i (pi i (u, v))
  have hH : MemW0 H := MemW0.fintype_tensor hf
  have hP : MemW0 P := by simpa [P] using hPullback
  have hG : MemW0 G := by simpa [G, P] using hP.aux_integral_slice
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [H] using hH
  · intro u
    simpa [P] using hP.aux_memW0_slice u
  · simpa [G] using hG
  · calc
      (∫ u : EuclideanSpace ℝ (Fin m),
          wienerEnvelope (fun u ↦ ∫ v, ∏ i, f i (pi i (u, v))) 1 u) =
          ∫ u, wienerEnvelope G 1 u := by rfl
      _ ≤ ∫ uv, wienerEnvelope P 1 uv :=
        aux_integral_wienerEnvelope_integral_slice_le hP
      _ ≤ C * ∫ x : ∀ i, EuclideanSpace ℝ (Fin (d i)), wienerEnvelope H 1 x := by
        simpa [P, H] using hPullback_bound
      _ ≤ C * ∏ i, ∫ x, wienerEnvelope (f i) 1 x :=
        mul_le_mul_of_nonneg_left (fintype_tensor_wienerNorm_le hf) hC
end Auto
