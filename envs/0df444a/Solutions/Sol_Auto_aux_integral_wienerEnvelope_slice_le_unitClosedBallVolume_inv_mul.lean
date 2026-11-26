-- Prove2me | solution 1 for Auto.aux_integral_wienerEnvelope_slice_le_unitClosedBallVolume_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:09.487132+00:00
-- url     : https://prove2.me/submissions/5fc3f256-c503-4e8c-809f-bbff0b7d76b5

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall
public import Theorems.Thm_Auto_MemW0_aux_integrable
public import Theorems.Thm_Auto_aux_unitClosedBallVolume_pos
public import Theorems.Thm_Auto_MemW0_aux_mem_wienerEnvelope_prod
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice_snd_of_addHaar

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) (u : EuclideanSpace ℝ (Fin m)) :
    (∫ v, wienerEnvelope (fun v => f (u, v)) 1 v) ≤
      (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1))⁻¹ *
        ∫ p, wienerEnvelope f 1 p := by
  let E := EuclideanSpace ℝ (Fin m)
  let F := EuclideanSpace ℝ (Fin l)
  let H : F → ℝ := fun v => wienerEnvelope (fun v => f (u, v)) 1 v
  let G : E × F → ℝ := wienerEnvelope f 1
  let B : Set E := closedBall u 1
  have hH : Integrable H := by
    simpa [H] using (hf.aux_memW0_slice u).2
  have hG : Integrable G := by
    simpa [G] using hf.2
  have hGW : MemW0 G := by
    simpa [G] using hf.aux_mem_wienerEnvelope_prod zero_le_one
  have hGslice (v : F) : Integrable (fun x : E => G (x, v)) :=
    (hGW.aux_memW0_slice_snd_of_addHaar v).aux_integrable
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  have hBfin : volume B ≠ ∞ := measure_closedBall_lt_top.ne
  have hpoint (v : F) :
      H v * volume.real B ≤ ∫ x in B, G (x, v) := by
    apply setIntegral_ge_of_const_le_real hBmeas hBfin
    · intro x hx
      change wienerEnvelope (fun v => f (u, v)) 1 v ≤ wienerEnvelope f 1 (x, v)
      unfold wienerEnvelope
      apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
      rintro _ ⟨z, hz, rfl⟩
      apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
      apply Metric.mem_closedBall.mpr
      rw [Prod.dist_eq]
      apply max_le
      · change dist u x ≤ 1
        simpa [B, Metric.mem_closedBall, dist_comm] using hx
      · simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    · exact (hGslice v).integrableOn
  let GI : E × F → ℝ := (B ×ˢ (univ : Set F)).indicator G
  have hGI : Integrable GI := by
    apply IntegrableOn.integrable_indicator hG.integrableOn
    exact hBmeas.prod MeasurableSet.univ
  have hGI_slice : Integrable (fun v : F => ∫ x : E, GI (x, v)) :=
    hGI.integral_prod_right
  have hGI_eq (v : F) : (∫ x : E, GI (x, v)) = ∫ x in B, G (x, v) := by
    change (∫ x : E, (B ×ˢ (univ : Set F)).indicator G (x, v)) = _
    have hfun : (fun x : E => (B ×ˢ (univ : Set F)).indicator G (x, v)) =
        B.indicator (fun x => G (x, v)) := by
      funext x
      by_cases hx : x ∈ B <;> simp [Set.indicator, hx]
    rw [hfun, integral_indicator hBmeas]
  have hmain : volume.real B * (∫ v, H v) ≤ ∫ p, G p := by
    calc
      volume.real B * (∫ v, H v) = ∫ v, H v * volume.real B := by
        rw [integral_mul_const]
        exact mul_comm _ _
      _ ≤ ∫ v, ∫ x in B, G (x, v) :=
        integral_mono (hH.mul_const _) (by simpa only [hGI_eq] using hGI_slice) hpoint
      _ = ∫ v, ∫ x : E, GI (x, v) := by
        congr with v
        exact (hGI_eq v).symm
      _ = ∫ p, GI p := (integral_prod_symm _ hGI).symm
      _ ≤ ∫ p, G p := by
        apply integral_mono hGI hG
        intro p
        by_cases hp : p ∈ B ×ˢ (univ : Set F)
        · simp [GI, hp]
        · change (B ×ˢ (univ : Set F)).indicator G p ≤ G p
          rw [Set.indicator_of_notMem hp]
          exact aux_wienerEnvelope_nonneg hf.1 zero_le_one p
  have hvol : volume.real B =
      volume.real (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) := by
    simpa [B] using MeasureTheory.Measure.addHaar_real_closedBall_center volume u 1
  let V : ℝ := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
  have hVpos : 0 < V := aux_unitClosedBallVolume_pos
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hmain' : V * (∫ v, H v) ≤ ∫ p, G p := by
    simpa [V, hvol] using hmain
  change (∫ v, H v) ≤ V⁻¹ * ∫ p, G p
  calc
    (∫ v, H v) = V⁻¹ * (V * ∫ v, H v) := by
      field_simp
    _ ≤ V⁻¹ * ∫ p, G p :=
      mul_le_mul_of_nonneg_left hmain' (inv_nonneg.mpr (le_of_lt hVpos))
end Auto
