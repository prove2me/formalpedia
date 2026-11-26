-- Prove2me | solution 1 for Auto.exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:02.349708+00:00
-- url     : https://prove2.me/submissions/e7399cd7-d0bd-4455-92bc-a4f1e0f5adb2

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice
public import Theorems.Thm_Auto_MemW0_aux_comp_injective_continuousLinearMap
public import Theorems.Thm_Auto_aux_exists_wienerEnvelope_comp_injective_continuousLinearMap_bound
public import Theorems.Thm_Auto_aux_integral_wienerEnvelope_slice_le_unitClosedBallVolume_inv_mul
public import Theorems.Thm_Auto_MemW0_aux_integral_slice
public import Theorems.Thm_Auto_aux_integral_wienerEnvelope_integral_slice_le
public import Theorems.Thm_Auto_MemW0_aux_comp_injective_continuousLinearMap_prod

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {m l n : ℕ} {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (π : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (hπ : Function.Injective π) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f : EuclideanSpace ℝ (Fin n) → K, MemW0 f →
      (∀ u : EuclideanSpace ℝ (Fin m),
        MemW0 (fun v : EuclideanSpace ℝ (Fin l) => f (π (u, v))) ∧
        (∫ v, wienerEnvelope (fun v : EuclideanSpace ℝ (Fin l) => f (π (u, v))) 1 v) ≤
          C₁ * ∫ y, wienerEnvelope f 1 y) ∧
      MemW0 (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, f (π (u, v))) ∧
      (∫ u, wienerEnvelope (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, f (π (u, v))) 1 u) ≤
        C₂ * ∫ y, wienerEnvelope f 1 y := by
  classical
  let : MeasureSpace (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) :=
    ⟨(volume : Measure (EuclideanSpace ℝ (Fin m))).prod
      (volume : Measure (EuclideanSpace ℝ (Fin l)))⟩
  let : Measure.IsAddHaarMeasure
      (volume : Measure (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l))) := by
    change Measure.IsAddHaarMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin m))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin l))))
    infer_instance
  let e : EuclideanSpace ℝ (Fin (m + l)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) :=
    EuclideanSpace.finAddEquivProd
  let g : EuclideanSpace ℝ (Fin (m + l)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    π.comp e.toContinuousLinearMap
  have hg : Function.Injective g := hπ.comp e.injective
  obtain ⟨Cg, hCg_pos, hCg⟩ :=
    aux_exists_wienerEnvelope_comp_injective_continuousLinearMap_bound (K := K) g hg
  obtain ⟨Ce, hCe_pos, hCe⟩ :=
    aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound (K := K) e.symm
  let B : ℝ := (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1))⁻¹
  have hB_pos : 0 < B := by
    have hball_pos : 0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
      apply ENNReal.toReal_pos
      · exact
          (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin m))) 0 zero_lt_one).trans_le
            (measure_mono ball_subset_closedBall) |>.ne'
      · exact measure_closedBall_lt_top.ne
    exact inv_pos.mpr (by simpa only [B] using hball_pos)
  refine ⟨B * (Ce * Cg), Ce * Cg, mul_pos hB_pos (mul_pos hCe_pos hCg_pos),
    mul_pos hCe_pos hCg_pos, ?_⟩
  intro f hf
  let P : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → K := fun uv => f (π uv)
  have hP : MemW0 P := by
    simpa only [P] using hf.aux_comp_injective_continuousLinearMap_prod π hπ
  have hH : MemW0 (f ∘ g) := hf.aux_comp_injective_continuousLinearMap g hg
  have hP_eq : ((f ∘ g) ∘ e.symm) = P := by
    funext uv
    simp only [Function.comp_apply, g, P, ContinuousLinearMap.comp_apply]
    change f (π (e (e.symm uv))) = f (π uv)
    rw [e.apply_symm_apply]
  have hP_bound : (∫ uv, wienerEnvelope P 1 uv) ≤
      (Ce * Cg) * ∫ y, wienerEnvelope f 1 y := by
    calc
      (∫ uv, wienerEnvelope P 1 uv) = ∫ uv, wienerEnvelope ((f ∘ g) ∘ e.symm) 1 uv := by
        rw [hP_eq]
      _ ≤ Ce * ∫ z, wienerEnvelope (f ∘ g) 1 z := hCe (f ∘ g) hH
      _ ≤ Ce * (Cg * ∫ y, wienerEnvelope f 1 y) :=
        mul_le_mul_of_nonneg_left (hCg f hf) hCe_pos.le
      _ = (Ce * Cg) * ∫ y, wienerEnvelope f 1 y := by ring
  have hG : MemW0 (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, f (π (u, v))) := by
    simpa only [P] using hP.aux_integral_slice
  refine ⟨?_, hG, ?_⟩
  · intro u
    have hslice_mem : MemW0 (fun v : EuclideanSpace ℝ (Fin l) => f (π (u, v))) := by
      simpa only [P] using hP.aux_memW0_slice u
    refine ⟨hslice_mem, ?_⟩
    calc
      (∫ v, wienerEnvelope (fun v : EuclideanSpace ℝ (Fin l) => f (π (u, v))) 1 v) ≤
          B * ∫ uv, wienerEnvelope P 1 uv := by
        simpa only [B, P] using
          aux_integral_wienerEnvelope_slice_le_unitClosedBallVolume_inv_mul hP u
      _ ≤ B * ((Ce * Cg) * ∫ y, wienerEnvelope f 1 y) :=
        mul_le_mul_of_nonneg_left hP_bound hB_pos.le
      _ = (B * (Ce * Cg)) * ∫ y, wienerEnvelope f 1 y := by ring
  · calc
      (∫ u, wienerEnvelope (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, f (π (u, v))) 1 u) ≤
          ∫ uv, wienerEnvelope P 1 uv := by
        simpa only [P] using aux_integral_wienerEnvelope_integral_slice_le hP
      _ ≤ (Ce * Cg) * ∫ y, wienerEnvelope f 1 y := hP_bound
end Auto
