-- Prove2me | solution 1 for ActuarialAnnuities.micro_mass_total
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:55:52.930264+00:00
-- url     : https://prove2.me/submissions/50d24dfe-e956-4c0c-b66a-bb61f916aebb

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bUDDMicroMass
open ActuarialAnnuities

theorem solution(h m : ℕ) (p : ℕ → ℝ) (hm : 0 < m) : bTotal (h*m) (bUDDMicroMass h m p) = bTotal h p := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold bTotal bUDDMicroMass
  rw [Finset.sum_range_succ, Finset.sum_range_succ, if_neg (lt_irrefl _), if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl (fun q hq => if_pos (Finset.mem_range.mp hq))]
  induction h with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    have hc : ∀ i ∈ Finset.range m, p ((k * m + i) / m) / (m : ℝ) = p k / m := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hi, zero_add]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
