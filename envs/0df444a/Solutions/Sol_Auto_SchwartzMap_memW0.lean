-- Prove2me | solution 1 for Auto.SchwartzMap.memW0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:59.767133+00:00
-- url     : https://prove2.me/submissions/82c09cb1-3b83-43c1-a3d3-40f5628740ae

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace SchwartzMap
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) 𝕜) :
    MemW0 f := by
  refine ⟨f.continuous, ?_⟩
  let C : ℝ := 2 ^ (d + 1) *
    (Finset.Iic (d + 1, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hC : ∀ y : EuclideanSpace ℝ (Fin d),
      (1 + ‖y‖) ^ (d + 1) * ‖f y‖ ≤ C := by
    intro y
    simpa [C] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d + 1, 0))
        le_rfl le_rfl f y)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound : ∀ x : EuclideanSpace ℝ (Fin d),
      wienerEnvelope f 1 x ≤ C * 2 ^ (d + 1) / (1 + ‖x‖) ^ (d + 1) := by
    intro x
    unfold wienerEnvelope
    apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
    rintro _ ⟨z, hz, rfl⟩
    have hz' : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hxy : 1 + ‖x‖ ≤ 2 * (1 + ‖x + z‖) := by
      calc
        1 + ‖x‖ ≤ 1 + (‖x + z‖ + ‖z‖) := by
          gcongr
          simpa using norm_sub_le (x + z) z
        _ ≤ 1 + (‖x + z‖ + 1) := by gcongr
        _ ≤ 2 * (1 + ‖x + z‖) := by nlinarith [norm_nonneg (x + z)]
    have hpow : (1 + ‖x‖) ^ (d + 1) ≤
        2 ^ (d + 1) * (1 + ‖x + z‖) ^ (d + 1) := by
      calc
        (1 + ‖x‖) ^ (d + 1) ≤ (2 * (1 + ‖x + z‖)) ^ (d + 1) :=
          pow_le_pow_left₀ (by positivity) hxy _
        _ = 2 ^ (d + 1) * (1 + ‖x + z‖) ^ (d + 1) := by rw [mul_pow]
    have hy : ‖f (x + z)‖ ≤ C / (1 + ‖x + z‖) ^ (d + 1) := by
      apply (le_div_iff₀ (pow_pos (by positivity) _)).mpr
      simpa [mul_comm] using hC (x + z)
    calc
      ‖f (x + z)‖ ≤ C / (1 + ‖x + z‖) ^ (d + 1) := hy
      _ = C * (1 / (1 + ‖x + z‖) ^ (d + 1)) := by ring
      _ ≤ C * (2 ^ (d + 1) / (1 + ‖x‖) ^ (d + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hC_nonneg
        apply (div_le_div_iff₀ (pow_pos (by positivity) _) (pow_pos (by positivity) _)).mpr
        simpa [mul_comm] using hpow
      _ = C * 2 ^ (d + 1) / (1 + ‖x‖) ^ (d + 1) := by ring
  have hrad : Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦
      (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ))) := by
    apply integrable_one_add_norm
    simp
  refine (hrad.const_mul (C * 2 ^ (d + 1))).mono_nonneg
    (continuous_wienerEnvelope f.continuous 1).aestronglyMeasurable
    (ae_of_all _ fun x ↦ aux_wienerEnvelope_nonneg f.continuous zero_le_one x)
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  exact hbound x
end SchwartzMap
end Auto
