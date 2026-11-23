-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableNormMulPowOfBounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:32.616304+00:00
-- url     : https://prove2.me/theorems/13097c31-5775-464f-bf5f-5343e59f8f5d
-- title:
--   Summable Norm Mul Pow Of Bounded
-- statement:
--   Definitions and structural lemmas for Summable Norm Mul Pow Of Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableNormMulPowOfBounded.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SummableSeriesBounds
open PowerSeries Filter Topology
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
def bdd (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] :
    Subring (PowerSeries C) where
  carrier := {Φ | ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b}
  mul_mem' := by
    rintro Φ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
    have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
    refine ⟨a * b, fun n => ?_⟩
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha0 hb0) ?_
    intro p _
    rw [norm_mul]
    exact mul_le_mul (ha _) (hb _) (norm_nonneg _) ha0
  one_mem' := ⟨1, fun n => by
    rw [coeff_one]; split_ifs <;> simp⟩
  add_mem' := by
    rintro Φ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun n => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (ha n) (hb n))
  zero_mem' := ⟨0, fun n => by simp⟩
  neg_mem' := by
    rintro Φ ⟨a, ha⟩
    exact ⟨a, fun n => by simpa using ha n⟩
theorem summable_norm_mul_pow_of_bounded {π : C} (hπ : ‖π‖ < 1) {a : ℕ → C} {b : ℝ} (hb : ∀ n, ‖a n‖ ≤ b) :
    Summable fun n => ‖a n * π ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg π) hπ).mul_left b)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hb n) (by positivity)
theorem summable_norm_bdd {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) :
    Summable fun n => ‖coeff n (Φ : PowerSeries C) * π ^ n‖ := by
  obtain ⟨b, hb⟩ := Φ.2
  exact summable_norm_mul_pow_of_bounded hπ hb
noncomputable def ev [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : bdd C →+* C where
  toFun Φ := ∑' n, coeff n (Φ : PowerSeries C) * π ^ n
  map_one' := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [coeff_one, hn]
  map_zero' := by simp
  map_add' Φ Ψ := by
    rw [← (summable_norm_bdd hπ Φ).of_norm.tsum_add (summable_norm_bdd hπ Ψ).of_norm]
    refine tsum_congr fun n => ?_
    simp [add_mul]
  map_mul' Φ Ψ := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_bdd hπ Φ)
      (summable_norm_bdd hπ Ψ)]
    refine tsum_congr fun n => ?_
    rw [Subring.coe_mul, coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = n := by simpa using hp
    rw [← hp', pow_add]
    ring
noncomputable def lin (π : C) : bdd C :=
  ⟨X - PowerSeries.C π, ⟨1 + ‖π‖, fun n => by
    rw [map_sub]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [coeff_X]; split_ifs <;> simp
    · rw [coeff_C]; split_ifs <;> simp⟩⟩
end GlobalTheory.SummableSeriesBounds


