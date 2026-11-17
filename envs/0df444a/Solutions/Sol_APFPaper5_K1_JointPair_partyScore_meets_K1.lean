-- Prove2me | solution 1 for APFPaper5.K1.JointPair.partyScore_meets_K1
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:18:57.846213+00:00
-- url     : https://prove2.me/submissions/c02991a6-b647-40f1-b02f-9917831067be

import Definitions.Def_APFPaper5_K1_party_score_joint_pair_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_party_score_joint_pair
title: The premises of the party-score K1 statement hold together with a joint record present: in the book of two own records and one joint record, costing 1, 1 and 3 together, the party score meets K1's typed conditions and the table of shared costs does not
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 22:13 HST: "B" (RULING_K1_score_with_joint_records_2026-11-14).
 Def_APFPaper5_K1_PartyScore, Thm_APFPaper5_K1_party_score, Thm_APFPaper5_K1_joint_pair_two_tables.
standing: A WORKED INSTANCE. It shows the statement partyScore_book_meets_K1 is not empty where a joint
 record is present, and that there the two candidate tables part ways. It is a book, not a world: no
 states, continuations or alignments, and the eight are not checked on it.
what this file says: with record 2 marked joint, the general keeping rule gives the joint-rule costs of
 pass 38 (0, 1, 1, 3: the numbers of this seat's residue world and of the codebank's parity pair); the
 party score meets K1's typed conditions; the table of shared costs of the same book is not faithful.
what this file does NOT say: that the residue world carries this book. No lane. No claim that the transfer
 is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Theorems.Thm_APFPaper5_K1_partyTo_book_iff
import Theorems.Thm_APFPaper5_K1_partyScore_book
import Theorems.Thm_APFPaper5_K1_partyScore_book_meets_K1
import Theorems.Thm_APFPaper5_K1_partyScore_book_faithful_iff
import Theorems.Thm_APFPaper5_K1_sharedCost_eq_partyScore_of_no_joint
import Definitions.Def_APFPaper5_K1_joint_pair_two_tables_Vocabulary
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_empty
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_zero
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_one
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_univ
import Theorems.Thm_APFPaper5_K1_JointPair_jointRule_sharedCost_table_not_faithful

set_option autoImplicit false

namespace APFPaper5.K1.JointPair



theorem keepsB_eq_everyPartyHeld :
    ∀ (S : Finset (Fin 2)) (a : Fin 3), keepsB mark joint S a = everyPartyHeld a S := by decide

theorem keptCost_eq_jointRuleCost : keptCost w (keepsB mark joint) = jointRuleCost := by
  funext S
  unfold keptCost jointRuleCost
  exact Finset.sum_congr rfl (fun a _ => by rw [keepsB_eq_everyPartyHeld])

/-- The costs of the book under the general keeping rule: 0, 1, 1 and 3 together. -/
theorem keptCost_values :
    keptCost w (keepsB mark joint) ∅ = 0 ∧ keptCost w (keepsB mark joint) {0} = 1 ∧
      keptCost w (keepsB mark joint) {1} = 1 ∧ keptCost w (keepsB mark joint) Finset.univ = 3 := by
  rw [keptCost_eq_jointRuleCost]
  exact ⟨jointRule_empty, jointRule_zero, jointRule_one, jointRule_univ⟩

/-- With the joint record present, the party score meets K1's typed conditions. -/
theorem partyScore_meets_K1 :
    IsBilinear (VP := Fin 2 → ℝ) (VE := Fin 2 → ℝ) (tableForm (partyScore w (keepsB mark joint))) ∧
      FaithfulNonnegDiagonal (tableForm (partyScore w (keepsB mark joint)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by
  have hown : ∀ i : Fin 2, ∃ a : Fin 3, 0 < w a ∧ ∀ j, mark j a = decide (j = i) := by
    intro i
    fin_cases i
    · exact ⟨0, by simp [w], by decide⟩
    · exact ⟨1, by simp [w], by decide⟩
  exact partyScore_book_meets_K1 w (fun a => by simp [w]) mark joint hown

/-- The table of shared costs of the same book is not faithful. -/
theorem sharedCost_table_not_faithful :
    ¬ FaithfulNonnegDiagonal
        (tableForm (fun i j => sharedCost (keptCost w (keepsB mark joint)) {i} {j}))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by
  rw [keptCost_eq_jointRuleCost]
  exact jointRule_sharedCost_table_not_faithful

end APFPaper5.K1.JointPair


theorem solution :
And
  (@APFPaper5.K1.IsBilinear.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
      Real.semiring (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommGroup)
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
      Real.semiring (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@APFPaper5.K1.tableForm.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@APFPaper5.K1.partyScore.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.JointPair.w
        (@APFPaper5.K1.keepsB.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) APFPaper5.K1.JointPair.mark
          APFPaper5.K1.JointPair.joint))))
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
      (@APFPaper5.K1.partyScore.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.JointPair.w
        (@APFPaper5.K1.keepsB.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) APFPaper5.K1.JointPair.mark
          APFPaper5.K1.JointPair.joint)))
    (@LinearEquiv.refl.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
      Real.semiring
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommMonoid)
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.JointPair.partyScore_meets_K1
