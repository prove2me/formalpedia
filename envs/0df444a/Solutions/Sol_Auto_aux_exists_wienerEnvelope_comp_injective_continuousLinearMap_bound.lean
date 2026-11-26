-- Prove2me | solution 1 for Auto.aux_exists_wienerEnvelope_comp_injective_continuousLinearMap_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:27.802543+00:00
-- url     : https://prove2.me/submissions/0d1eaf51-9bb0-4645-aad3-3f2e8973a2c4

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_comp_continuousLinearMap_of_measurePreserving
public import Theorems.Thm_Auto_aux_orthogonalDecomposition_range_apply
public import Theorems.Thm_Auto_aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound
public import Theorems.Thm_Auto_aux_integrable_wienerEnvelope_of_integrable
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice_snd_of_addHaar
public import Theorems.Thm_Auto_aux_integral_wienerEnvelope_slice_snd_le_unitClosedBallVolume_inv_mul_addHaar

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {k n : ℕ} {K : Type*} [NormedAddCommGroup K]
    (π : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hπ : Function.Injective π) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → K, MemW0 f →
      (∫ x, wienerEnvelope (f ∘ π) 1 x) ≤ C * ∫ y, wienerEnvelope f 1 y := by
  classical
  let s : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := π.range
  let : MeasureSpace (s × sᗮ) :=
    ⟨(volume : Measure s).prod (volume : Measure sᗮ)⟩
  let : Measure.IsAddHaarMeasure (volume : Measure (s × sᗮ)) := by
    change Measure.IsAddHaarMeasure ((volume : Measure s).prod (volume : Measure sᗮ))
    infer_instance
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] s × sᗮ :=
    s.orthogonalDecomposition.toContinuousLinearEquiv.trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ s sᗮ)
  let q : EuclideanSpace ℝ (Fin k) ≃L[ℝ] s :=
    π.equivRange hπ π.range.closed_of_finiteDimensional
  obtain ⟨Cq, hCq_pos, hCq⟩ :=
    aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound (K := K) q
  obtain ⟨Ce, hCe_pos, hCe⟩ :=
    aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound (K := K) e.symm
  let V : ℝ := ((volume : Measure sᗮ).real (closedBall 0 1))⁻¹
  have hV_pos : 0 < V := by
    have hball_pos : 0 < (volume : Measure sᗮ).real (closedBall (0 : sᗮ) 1) := by
      apply ENNReal.toReal_pos
      · exact (measure_ball_pos (volume : Measure sᗮ) 0 zero_lt_one).trans_le
          (measure_mono ball_subset_closedBall) |>.ne'
      · exact measure_closedBall_lt_top.ne
    exact inv_pos.mpr (by simpa only [V] using hball_pos)
  refine ⟨Cq * V * Ce, mul_pos (mul_pos hCq_pos hV_pos) hCe_pos, ?_⟩
  intro f hf
  let F : s × sᗮ → K := f ∘ e.symm
  have hF : MemW0 F := by
    have he : MeasurePreserving e := by
      let e₁ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] WithLp 2 (s × sᗮ) :=
        s.orthogonalDecomposition
      let e₂ : WithLp 2 (s × sᗮ) ≃L[ℝ] s × sᗮ :=
        WithLp.prodContinuousLinearEquiv 2 ℝ s sᗮ
      change MeasurePreserving (e₂ ∘ e₁)
      exact (WithLp.volume_preserving_ofLp s sᗮ).comp e₁.measurePreserving
    have he_symm : MeasurePreserving e.symm :=
      MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv he
    apply hf.aux_comp_continuousLinearMap_of_measurePreserving e.symm.toContinuousLinearMap he_symm
    exact aux_integrable_wienerEnvelope_of_integrable hf.1 zero_lt_one
      (norm_nonneg e.symm.toContinuousLinearMap) hf.2
  have hS : MemW0 (fun u : s => F (u, 0)) :=
    hF.aux_memW0_slice_snd_of_addHaar 0
  have hslice : (∫ u, wienerEnvelope (fun u : s => F (u, 0)) 1 u) ≤
      V * ∫ p, wienerEnvelope F 1 p := by
    simpa only [V] using
      aux_integral_wienerEnvelope_slice_snd_le_unitClosedBallVolume_inv_mul_addHaar hF 0
  have hq_bound := hCq (fun u : s => F (u, 0)) hS
  have he_bound : (∫ p, wienerEnvelope F 1 p) ≤ Ce * ∫ y, wienerEnvelope f 1 y := by
    simpa only [F] using hCe f hf
  have hfun : (fun x : EuclideanSpace ℝ (Fin k) => F (q x, 0)) = f ∘ π := by
    funext x
    have hcoord : e (π x) = (q x, 0) := by
      rw [aux_orthogonalDecomposition_range_apply π x]
      apply Prod.ext
      · change π.rangeRestrict x = (π.equivRange hπ π.range.closed_of_finiteDimensional) x
        exact congrFun (π.coe_equivRange hπ π.range.closed_of_finiteDimensional).symm x
      · rfl
    change f (e.symm (q x, 0)) = f (π x)
    rw [← hcoord, e.symm_apply_apply]
  calc
    (∫ x, wienerEnvelope (f ∘ π) 1 x) =
        ∫ x, wienerEnvelope ((fun u : s => F (u, 0)) ∘ q) 1 x := by
      simpa only [Function.comp_def] using
        congrArg (fun g : EuclideanSpace ℝ (Fin k) → K => ∫ x, wienerEnvelope g 1 x) hfun.symm
    _ ≤ Cq * ∫ u, wienerEnvelope (fun u : s => F (u, 0)) 1 u := hq_bound
    _ ≤ Cq * (V * ∫ p, wienerEnvelope F 1 p) :=
      mul_le_mul_of_nonneg_left hslice hCq_pos.le
    _ ≤ Cq * (V * (Ce * ∫ y, wienerEnvelope f 1 y)) := by
      gcongr
    _ = (Cq * V * Ce) * ∫ y, wienerEnvelope f 1 y := by ring
end Auto
