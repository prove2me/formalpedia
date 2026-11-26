-- Prove2me | solution 1 for Auto.MemW0.memLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:14.591202+00:00
-- url     : https://prove2.me/submissions/d76551aa-6d29-4453-8b4e-a8189ca45fca

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_continuous
public import Theorems.Thm_Auto_MemW0_aux_integrable
public import Theorems.Thm_Auto_aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume
public import Theorems.Thm_Auto_MemW0_aux_memLp_top

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp f p volume := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · exact hf.aux_memLp_top
  have hp_zero : p ≠ 0 := by
    intro hp_zero
    rw [hp_zero] at hp
    norm_num at hp
  apply (integrable_norm_rpow_iff hf.aux_continuous.aestronglyMeasurable hp_zero hp_top).mp
  let C : ℝ := max 1 ((∫ y, wienerEnvelope f 1 y) /
    volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1))
  have hC : ∀ x, ‖f x‖ ≤ C := by
    intro x
    exact (aux_norm_le_integral_wienerEnvelope_div_unitClosedBallVolume hf x).trans
      (le_max_right _ _)
  have hp_real : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp_top hp
  have hp_sub : 0 ≤ p.toReal - 1 := sub_nonneg.mpr hp_real
  refine (hf.aux_integrable.norm.const_mul (C ^ (p.toReal - 1))).mono' ?_ ?_
  · exact ((Real.continuous_rpow_const ENNReal.toReal_nonneg).comp hf.aux_continuous.norm)
      |>.aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      ‖f x‖ ^ p.toReal = ‖f x‖ ^ (p.toReal - 1) * ‖f x‖ := by
        calc
          ‖f x‖ ^ p.toReal = ‖f x‖ ^ ((p.toReal - 1) + 1) := by
            congr 1
            linarith
          _ = ‖f x‖ ^ (p.toReal - 1) * ‖f x‖ ^ 1 :=
            Real.rpow_add_of_nonneg (norm_nonneg _) hp_sub zero_le_one
          _ = ‖f x‖ ^ (p.toReal - 1) * ‖f x‖ := by simp
      _ ≤ C ^ (p.toReal - 1) * ‖f x‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hC x) hp_sub)
          (norm_nonneg _)
end MemW0
end Auto
