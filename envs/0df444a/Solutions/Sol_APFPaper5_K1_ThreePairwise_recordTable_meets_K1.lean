-- Prove2me | solution 1 for APFPaper5.K1.ThreePairwise.recordTable_meets_K1
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:58:34.481641+00:00
-- url     : https://prove2.me/submissions/1dcbe883-1e4d-4e7f-9cc8-ce8b7626f9d8

import Definitions.Def_APFPaper5_K1_three_pairwise_joint_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_three_pairwise_joint
title: Three distinctions with a joint record on each pair: the pair bound on every pair does not give K1's conditions for the table of shared costs, at the floor that table's form is negative, and the record-book table meets K1's conditions
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 21:51 HST: "Tee up decision then finish it". Builder seat: tableForm,
 sharedCost, IsBilinear, FaithfulNonnegDiagonal. This seat: dominant_table_meets_K1 (pass 37).
standing: WORKED INSTANCES on three marks, as tables and as a cost function. No input is consumed. No world
 meeting the eight is built here; whether three distinctions may each be related to the other two in one
 counted family is NOT settled (the unit rule of 21:15 HST as typed does not forbid it).
what this file says:
 - tripleCost c: each distinction costs 1 and each pair held together adds a joint record of cost c. Its
   table of shared costs is 1 on the diagonal and -c off it.
 - With c = 3/5 every pair meets the pair bound strictly, yet the form is negative on (1, 1, 1). So for
   three or more the pair bound on each pair is not enough.
 - With c = 1 (each joint record at the cost of a distinction, as in the residue world and the codebank's
   parity pair) the form on (1, 1, 1) is -3.
 - The record-book table for c = 1 (each distinction party to its own record and to two joint records: 3
   on the diagonal, 1 off it) meets K1's typed conditions.
what this file does NOT say:
 - That the record-book table is K1's score. Not ruled.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that Born
   is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_dominant_table_Vocabulary
import Theorems.Thm_APFPaper5_K1_dominant_table_lower_bound
import Theorems.Thm_APFPaper5_K1_dominant_table_meets_K1
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
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace APFPaper5.K1.ThreePairwise



theorem form_on_ones (d c : ℝ) :
    tableForm (uniformTable d c) (fun _ => 1) (fun _ => 1) = 3 * d + 6 * c := by
  simp [tableForm, uniformTable, Fin.sum_univ_three]
  ring



theorem sharedCost_tripleCost (c : ℝ) (i j : Fin 3) :
    sharedCost (tripleCost c) {i} {j} = uniformTable 1 (-c) i j := by
  unfold sharedCost tripleCost uniformTable
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h, ← Finset.insert_eq, Finset.card_pair h]
    norm_num [Nat.choose]

/-- The pair bound holds strictly on every pair, and the form is negative on (1, 1, 1). -/
theorem pair_bound_on_every_pair_is_not_enough :
    (∀ i j : Fin 3, i ≠ j →
        sharedCost (tripleCost (3 / 5)) {i} {j} * sharedCost (tripleCost (3 / 5)) {i} {j} <
          sharedCost (tripleCost (3 / 5)) {i} {i} * sharedCost (tripleCost (3 / 5)) {j} {j}) ∧
      tableForm (fun i j => sharedCost (tripleCost (3 / 5)) {i} {j}) (fun _ => 1) (fun _ => 1) < 0 := by
  have htab : (fun i j => sharedCost (tripleCost (3 / 5)) {i} {j}) = uniformTable 1 (-(3 / 5)) := by
    funext i j
    exact sharedCost_tripleCost _ i j
  refine ⟨fun i j hij => ?_, ?_⟩
  · rw [sharedCost_tripleCost, sharedCost_tripleCost, sharedCost_tripleCost]
    unfold uniformTable
    rw [if_neg hij, if_pos rfl, if_pos rfl]
    norm_num
  · rw [htab, form_on_ones]
    norm_num

/-- So that table does not have a nonnegative diagonal. -/
theorem pair_bound_table_fails_K1 :
    ¬ FaithfulNonnegDiagonal (tableForm (fun i j => sharedCost (tripleCost (3 / 5)) {i} {j}))
        (LinearEquiv.refl ℝ (Fin 3 → ℝ)) := by
  intro h
  have h1 : 0 ≤ tableForm (fun i j => sharedCost (tripleCost (3 / 5)) {i} {j}) (fun _ => 1) (fun _ => 1) :=
    h.1 (fun _ => 1)
  linarith [pair_bound_on_every_pair_is_not_enough.2]

/-- At the floor (each joint record costs what a distinction costs) the form on (1, 1, 1) is -3. -/
theorem at_the_floor_form_is_negative :
    tableForm (fun i j => sharedCost (tripleCost 1) {i} {j}) (fun _ => 1) (fun _ => 1) = -3 := by
  have htab : (fun i j => sharedCost (tripleCost 1) {i} {j}) = uniformTable 1 (-1) := by
    funext i j
    exact sharedCost_tripleCost _ i j
  rw [htab, form_on_ones]
  norm_num

/-- The record-book table at the floor: each distinction is party to its own record and to two joint
records (3 on the diagonal), and each pair is party to one joint record (1 off it). It meets K1's typed
conditions. -/
theorem recordTable_meets_K1 :
    IsBilinear (VP := Fin 3 → ℝ) (VE := Fin 3 → ℝ) (tableForm (uniformTable 3 1)) ∧
      FaithfulNonnegDiagonal (tableForm (uniformTable 3 1)) (LinearEquiv.refl ℝ (Fin 3 → ℝ)) := by
  apply dominant_table_meets_K1
  · intro i j
    unfold uniformTable
    by_cases h : i = j
    · subst h
      rfl
    · have h' : ¬ j = i := fun e => h e.symm
      rw [if_neg h, if_neg h']
  · intro i
    fin_cases i <;> simp [offSize, uniformTable, Fin.sum_univ_three] <;> norm_num

end APFPaper5.K1.ThreePairwise


theorem solution :
And
  (@APFPaper5.K1.IsBilinear.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Real
      Real.semiring (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Real
      Real.semiring (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@APFPaper5.K1.tableForm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (APFPaper5.K1.ThreePairwise.uniformTable
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
  (@APFPaper5.K1.FaithfulNonnegDiagonal.{0, 0}
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Real
      Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Real
      Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
    (@APFPaper5.K1.tableForm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (APFPaper5.K1.ThreePairwise.uniformTable
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (@LinearEquiv.refl.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
      Real.semiring
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real.instAddCommMonoid)
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.ThreePairwise.recordTable_meets_K1
