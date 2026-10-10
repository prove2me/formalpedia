-- Prove2me | solution 1 for ActuarialValuation.dbPCLSMaximum_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:26.038618+00:00
-- url     : https://prove2.me/submissions/2c8b1888-aeb2-4104-ae19-5df05322101c

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash
import Definitions.Def_actuarial_dbCommutationHeadroom
import Definitions.Def_actuarial_dbCappedPCLS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f A : ℝ)
  (hg : 0 ≤ g) (hf : 0 < f) (hA : 0 ≤ A) :
  (dbCommutationHeadroom g (dbHMRCMaximumCash g f) f = 0) ∧
  (0 ≤ dbCappedPCLS g f A) ∧
  (dbCappedPCLS g f A ≤ dbHMRCMaximumCash g f) ∧
  (dbCappedPCLS g f A ≤ A) ∧
  (0 ≤ dbCommutationHeadroom g (dbCappedPCLS g f A) f) := by
  have hfn : f ≠ 0 := ne_of_gt hf
  have hd : (0 : ℝ) < 20 + 3*f := by linarith
  have hmaxzero : dbCommutationHeadroom g (dbHMRCMaximumCash g f) f = 0 := by
    unfold dbCommutationHeadroom dbCommutedPension dbHMRCMaximumCash
    field_simp
    ring
  have hmaxnonneg : 0 ≤ dbHMRCMaximumCash g f := by
    unfold dbHMRCMaximumCash
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 20) (le_of_lt hf)) hg
    · exact le_of_lt hd
  have hcap_nonneg : 0 ≤ dbCappedPCLS g f A := by
    unfold dbCappedPCLS
    exact le_min hmaxnonneg hA
  have hcap_le_max : dbCappedPCLS g f A ≤ dbHMRCMaximumCash g f := by
    unfold dbCappedPCLS
    exact min_le_left _ _
  have hcap_le_A : dbCappedPCLS g f A ≤ A := by
    unfold dbCappedPCLS
    exact min_le_right _ _
  have hcap_headroom : 0 ≤ dbCommutationHeadroom g (dbCappedPCLS g f A) f := by
    have hbound : dbCappedPCLS g f A * (20 + 3*f) ≤ 20*f*g := by
      apply (le_div_iff₀ hd).1
      simpa only [dbHMRCMaximumCash] using hcap_le_max
    have hidentity :
        dbCommutationHeadroom g (dbCappedPCLS g f A) f =
          (20*f*g - (20+3*f)*dbCappedPCLS g f A) / f := by
      unfold dbCommutationHeadroom dbCommutedPension
      field_simp
      ring
    rw [hidentity]
    apply div_nonneg
    · nlinarith
    · exact le_of_lt hf
  exact ⟨hmaxzero, hcap_nonneg, hcap_le_max, hcap_le_A, hcap_headroom⟩
