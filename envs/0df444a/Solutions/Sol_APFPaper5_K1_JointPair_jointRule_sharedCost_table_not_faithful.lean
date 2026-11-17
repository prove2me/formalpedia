-- Prove2me | solution 1 for APFPaper5.K1.JointPair.jointRule_sharedCost_table_not_faithful
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:45:50.484895+00:00
-- url     : https://prove2.me/submissions/10759271-ae42-4dd3-88c8-f4ae7fef3d18

import Definitions.Def_APFPaper5_K1_joint_pair_two_tables_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_joint_pair_two_tables
title: One book of three records under two rules for when a record is kept: the record-book table is the same under both and meets K1's typed conditions; the table of shared costs agrees with it under the shared rule and, under the joint rule, is not faithful
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:51 HST: "Tee up decision then finish it". Read as: lay out the call on
 joint records with its facts typed. Builder seat: atomTable, tableForm, record_book_table_satisfies_K1,
 sharedCost. Numbers: the joint-rule costs 1, 1 and 3 are those of this seat's residue world
 (Thm_APFB06_subadditivity_worlds, APFB06.ResidueWorldR2: cost_single_A, cost_single_B, cost_pair, a world
 meeting the eight) and of the codebank's parity pair
 (apf/delta_calculus.py line 1180: 3*EPS - EPS - EPS). The shared-rule costs 2, 2 and 3 are those of this
 seat's bridge witness (pass 26).
standing: A WORKED INSTANCE with two distinctions. It decides nothing about what K1's score IS. That is a
 call for the author (TEE_UP_K1_score_with_joint_records_2026-11-14). No input is consumed.
what this file says:
 - The book: one record of cost 1 for each distinction and one record of cost 1 that both are party to.
 - Shared rule (a record is kept when SOME distinction party to it is held): costs 0, 2, 2, 3. The table of
   shared costs IS the record-book table: 2 on the diagonal, 1 off it.
 - Joint rule (a record is kept when EVERY distinction party to it is held): costs 0, 1, 1, 3. The table of
   shared costs is 1 on the diagonal and -1 off it; its form vanishes on (1, 1); it is not faithful. The
   record-book table is unchanged. Its diagonal entry is what a distinction adds over the other, and its
   off-diagonal entry is the cost of the joint record, which is minus the shared cost.
 - The record-book table meets K1's typed conditions (the builder seat's theorem, applied).
what this file does NOT say:
 - That the record-book table is K1's score where a joint record is present. Not ruled.
 - That costs alone fix the book. They do not: costs fix only the difference between what two distinctions
   share and what joins them. The table here reads the records.
 - Anything for three or more distinctions (see Thm_APFPaper5_K1_three_pairwise_joint).
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Theorems.Thm_APFPaper5_K1_sharedCost_self
import Theorems.Thm_APFPaper5_K1_sharedCost_le_right
import Theorems.Thm_APFPaper5_K1_sharedCost_le_left
import Theorems.Thm_APFPaper5_K1_sharedCost_nonneg_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_ledger
import Theorems.Thm_APFPaper5_K1_sharedCost_channel_no_joint
import Theorems.Thm_APFPaper5_K1_cost_is_count_times_floor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper5.K1.JointPair













theorem pair_union : (({0} : Finset (Fin 2)) ∪ {1}) = Finset.univ := by decide

theorem pair_union' : (({1} : Finset (Fin 2)) ∪ {0}) = Finset.univ := by decide

/-! ### The costs under each rule -/

theorem sharedRule_empty : sharedRuleCost ∅ = 0 := by
  have h : ∀ a, somePartyHeld a ∅ = false := by decide
  unfold sharedRuleCost
  rw [Fin.sum_univ_three, h 0, h 1, h 2]
  norm_num [ind, w]

theorem sharedRule_zero : sharedRuleCost {0} = 2 := by
  have h0 : somePartyHeld 0 {0} = true := by decide
  have h1 : somePartyHeld 1 {0} = false := by decide
  have h2 : somePartyHeld 2 {0} = true := by decide
  unfold sharedRuleCost
  rw [Fin.sum_univ_three, h0, h1, h2]
  norm_num [ind, w]

theorem sharedRule_one : sharedRuleCost {1} = 2 := by
  have h0 : somePartyHeld 0 {1} = false := by decide
  have h1 : somePartyHeld 1 {1} = true := by decide
  have h2 : somePartyHeld 2 {1} = true := by decide
  unfold sharedRuleCost
  rw [Fin.sum_univ_three, h0, h1, h2]
  norm_num [ind, w]

theorem sharedRule_univ : sharedRuleCost Finset.univ = 3 := by
  have h : ∀ a, somePartyHeld a Finset.univ = true := by decide
  unfold sharedRuleCost
  rw [Fin.sum_univ_three, h 0, h 1, h 2]
  norm_num [ind, w]

theorem jointRule_empty : jointRuleCost ∅ = 0 := by
  have h : ∀ a, everyPartyHeld a ∅ = false := by decide
  unfold jointRuleCost
  rw [Fin.sum_univ_three, h 0, h 1, h 2]
  norm_num [ind, w]

theorem jointRule_zero : jointRuleCost {0} = 1 := by
  have h0 : everyPartyHeld 0 {0} = true := by decide
  have h1 : everyPartyHeld 1 {0} = false := by decide
  have h2 : everyPartyHeld 2 {0} = false := by decide
  unfold jointRuleCost
  rw [Fin.sum_univ_three, h0, h1, h2]
  norm_num [ind, w]

theorem jointRule_one : jointRuleCost {1} = 1 := by
  have h0 : everyPartyHeld 0 {1} = false := by decide
  have h1 : everyPartyHeld 1 {1} = true := by decide
  have h2 : everyPartyHeld 2 {1} = false := by decide
  unfold jointRuleCost
  rw [Fin.sum_univ_three, h0, h1, h2]
  norm_num [ind, w]

theorem jointRule_univ : jointRuleCost Finset.univ = 3 := by
  have h : ∀ a, everyPartyHeld a Finset.univ = true := by decide
  unfold jointRuleCost
  rw [Fin.sum_univ_three, h 0, h 1, h 2]
  norm_num [ind, w]

/-! ### The record-book table: the same under both rules -/

theorem recordTable_values :
    atomTable w mark 0 0 = 2 ∧ atomTable w mark 0 1 = 1 ∧ atomTable w mark 1 0 = 1 ∧
      atomTable w mark 1 1 = 2 := by
  have m00 : mark 0 0 = true := by decide
  have m01 : mark 0 1 = false := by decide
  have m02 : mark 0 2 = true := by decide
  have m10 : mark 1 0 = false := by decide
  have m11 : mark 1 1 = true := by decide
  have m12 : mark 1 2 = true := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold atomTable
    rw [Fin.sum_univ_three, m00, m01, m02]
    norm_num [ind, w]
  · unfold atomTable
    rw [Fin.sum_univ_three, m00, m01, m02, m10, m11, m12]
    norm_num [ind, w]
  · unfold atomTable
    rw [Fin.sum_univ_three, m00, m01, m02, m10, m11, m12]
    norm_num [ind, w]
  · unfold atomTable
    rw [Fin.sum_univ_three, m10, m11, m12]
    norm_num [ind, w]

/-- The record-book table meets K1's typed conditions. -/
theorem recordTable_meets_K1 :
    IsBilinear (VP := Fin 2 → ℝ) (VE := Fin 2 → ℝ) (tableForm (atomTable w mark)) ∧
      FaithfulNonnegDiagonal (tableForm (atomTable w mark)) (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by
  have hsingle : ∀ i : Fin 2, ∃ a : Fin 3, 0 < w a ∧ ∀ j, mark j a = decide (j = i) := by
    intro i
    fin_cases i
    · exact ⟨0, by simp [w], by decide⟩
    · exact ⟨1, by simp [w], by decide⟩
  exact record_book_table_satisfies_K1 w (fun a => by simp [w]) mark hsingle

/-! ### Shared rule: the table of shared costs is the record-book table -/

theorem sharedRule_table_is_recordTable (i j : Fin 2) :
    sharedCost sharedRuleCost {i} {j} = atomTable w mark i j := by
  obtain ⟨h00, h01, h10, h11⟩ := recordTable_values
  fin_cases i <;> fin_cases j
  · show sharedCost sharedRuleCost {0} {0} = atomTable w mark 0 0
    rw [sharedCost_self, sharedRule_zero, h00]
  · show sharedCost sharedRuleCost {0} {1} = atomTable w mark 0 1
    unfold sharedCost
    rw [pair_union, sharedRule_zero, sharedRule_one, sharedRule_univ, h01]
    norm_num
  · show sharedCost sharedRuleCost {1} {0} = atomTable w mark 1 0
    unfold sharedCost
    rw [pair_union', sharedRule_zero, sharedRule_one, sharedRule_univ, h10]
    norm_num
  · show sharedCost sharedRuleCost {1} {1} = atomTable w mark 1 1
    rw [sharedCost_self, sharedRule_one, h11]

/-! ### Joint rule: the table of shared costs is not the record-book table, and is not faithful -/

theorem jointRule_sharedCost_values :
    sharedCost jointRuleCost {0} {0} = 1 ∧ sharedCost jointRuleCost {0} {1} = -1 ∧
      sharedCost jointRuleCost {1} {0} = -1 ∧ sharedCost jointRuleCost {1} {1} = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sharedCost_self, jointRule_zero]
  · unfold sharedCost
    rw [pair_union, jointRule_zero, jointRule_one, jointRule_univ]
    norm_num
  · unfold sharedCost
    rw [pair_union', jointRule_zero, jointRule_one, jointRule_univ]
    norm_num
  · rw [sharedCost_self, jointRule_one]

/-- Under the joint rule the form of the table of shared costs vanishes on (1, 1). -/
theorem jointRule_sharedCost_form_vanishes :
    tableForm (fun i j => sharedCost jointRuleCost {i} {j}) (fun _ => 1) (fun _ => 1) = 0 := by
  obtain ⟨h00, h01, h10, h11⟩ := jointRule_sharedCost_values
  simp [tableForm, Fin.sum_univ_two, h00, h01, h10, h11]

theorem jointRule_sharedCost_table_not_faithful :
    ¬ FaithfulNonnegDiagonal (tableForm (fun i j => sharedCost jointRuleCost {i} {j}))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by
  intro h
  have hx : (fun _ : Fin 2 => (1 : ℝ)) = 0 := h.2 (fun _ => 1) jointRule_sharedCost_form_vanishes
  have h0 := congrFun hx 0
  simp at h0

/-- Under the joint rule the record-book table reads: on the diagonal, what a distinction adds over the
other; off it, the cost of the joint record, which is minus the shared cost. -/
theorem jointRule_recordTable_reads :
    atomTable w mark 0 0 = jointRuleCost Finset.univ - jointRuleCost {1} ∧
      atomTable w mark 1 1 = jointRuleCost Finset.univ - jointRuleCost {0} ∧
      atomTable w mark 0 1 = -sharedCost jointRuleCost {0} {1} ∧
      atomTable w mark 1 0 = -sharedCost jointRuleCost {1} {0} := by
  obtain ⟨h00, h01, h10, h11⟩ := recordTable_values
  obtain ⟨_, s01, s10, _⟩ := jointRule_sharedCost_values
  rw [h00, h01, h10, h11, s01, s10, jointRule_univ, jointRule_zero, jointRule_one]
  norm_num

end APFPaper5.K1.JointPair


theorem solution :
Not
  (@APFPaper5.K1.FaithfulNonnegDiagonal.{0, 0}
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
      Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
      Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
    (@APFPaper5.K1.tableForm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      fun (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
      @APFPaper5.K1.sharedCost.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        APFPaper5.K1.JointPair.jointRuleCost
        (@Singleton.singleton.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Finset.instSingleton.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) i)
        (@Singleton.singleton.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Finset.instSingleton.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) j))
    (@LinearEquiv.refl.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
      Real.semiring
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommMonoid)
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.JointPair.jointRule_sharedCost_table_not_faithful
