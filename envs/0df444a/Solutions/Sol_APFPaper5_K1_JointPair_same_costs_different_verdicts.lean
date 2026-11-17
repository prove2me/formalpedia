-- Prove2me | solution 1 for APFPaper5.K1.JointPair.same_costs_different_verdicts
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:28:25.090516+00:00
-- url     : https://prove2.me/submissions/7604b80b-fd18-4ce4-a6f4-88c9edc9afac

import Definitions.Def_APFPaper5_K1_same_costs_two_books_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_same_costs_two_books
title: Two books with the same listing and the same cost for every family: in one a joint record of cost 1 and the party score meets K1's typed conditions; in the other a shared record of cost -1 and the party score is not faithful
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 05:07 HST: "1 Confirmed, please proceed" (item 5 of this seat's list of
 05:00 HST). Def_APFPaper5_K1_PartyScore, Thm_APFPaper5_K1_party_score_joint_pair.
standing: A WORKED INSTANCE on books (keeping rules with record costs), not on a record ledger and not a
 world. It shows that "no record costs less than nothing" cannot be derived from anything said about
 family costs: the two books cost every family the same (0, 1, 1 and 3 together) and differ on it. On a
 record ledger the question does not arise, because a record's cost is typed nonnegative there, as the
 declared calibration is. The second book is therefore NOT a record ledger.
what this file says: book one is the joint pair of pass 39 (own records 1 and 1, a joint record 1). Book
 two has the same listing with own records costing 2 and 2 and the common record costing -1, kept under
 the shared rule. Every family costs the same in both. The party score of book one meets K1's typed
 conditions. The party score of book two is 1 on the diagonal and -1 off it, and is not faithful.
what this file does NOT say: that a record may cost less than nothing. No lane. No claim that the transfer
 is forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_party_score_joint_pair_Vocabulary
import Theorems.Thm_APFPaper5_K1_JointPair_keptCost_eq_jointRuleCost
import Theorems.Thm_APFPaper5_K1_JointPair_partyScore_meets_K1

set_option autoImplicit false

namespace APFPaper5.K1.JointPair





theorem signed_keeps :
    ∀ (S : Finset (Fin 2)) (a : Fin 3), keepsB mark noJoint S a = somePartyHeld a S := by decide

theorem signed_cost (S : Finset (Fin 2)) :
    keptCost wSigned (keepsB mark noJoint) S =
      wSigned 0 * ind (somePartyHeld 0 S) + wSigned 1 * ind (somePartyHeld 1 S) +
        wSigned 2 * ind (somePartyHeld 2 S) := by
  unfold keptCost
  rw [Fin.sum_univ_three, signed_keeps, signed_keeps, signed_keeps]

theorem finset_fin2_cases :
    ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = Finset.univ := by decide

/-- The two books cost every family the same. -/
theorem same_costs : keptCost wSigned (keepsB mark noJoint) = keptCost w (keepsB mark joint) := by
  funext S
  rw [keptCost_eq_jointRuleCost, signed_cost]
  rcases finset_fin2_cases S with rfl | rfl | rfl | rfl
  · have h : ∀ a, somePartyHeld a ∅ = false := by decide
    rw [h 0, h 1, h 2, jointRule_empty]
    norm_num [ind]
  · have h0 : somePartyHeld 0 {0} = true := by decide
    have h1 : somePartyHeld 1 {0} = false := by decide
    have h2 : somePartyHeld 2 {0} = true := by decide
    rw [h0, h1, h2, jointRule_zero]
    norm_num [ind, wSigned]
  · have h0 : somePartyHeld 0 {1} = false := by decide
    have h1 : somePartyHeld 1 {1} = true := by decide
    have h2 : somePartyHeld 2 {1} = true := by decide
    rw [h0, h1, h2, jointRule_one]
    norm_num [ind, wSigned]
  · have h : ∀ a, somePartyHeld a Finset.univ = true := by decide
    rw [h 0, h 1, h 2, jointRule_univ]
    norm_num [ind, wSigned]

/-- The party score of book two: 1 on the diagonal, -1 off it. -/
theorem signed_partyScore_values :
    partyScore wSigned (keepsB mark noJoint) 0 0 = 1 ∧
      partyScore wSigned (keepsB mark noJoint) 0 1 = -1 ∧
      partyScore wSigned (keepsB mark noJoint) 1 0 = -1 ∧
      partyScore wSigned (keepsB mark noJoint) 1 1 = 1 := by
  rw [partyScore_book]
  have m00 : mark 0 0 = true := by decide
  have m01 : mark 0 1 = false := by decide
  have m02 : mark 0 2 = true := by decide
  have m10 : mark 1 0 = false := by decide
  have m11 : mark 1 1 = true := by decide
  have m12 : mark 1 2 = true := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold atomTable
    rw [Fin.sum_univ_three, m00, m01, m02]
    norm_num [ind, wSigned]
  · unfold atomTable
    rw [Fin.sum_univ_three, m00, m01, m02, m10, m11, m12]
    norm_num [ind, wSigned]
  · unfold atomTable
    rw [Fin.sum_univ_three, m00, m01, m02, m10, m11, m12]
    norm_num [ind, wSigned]
  · unfold atomTable
    rw [Fin.sum_univ_three, m10, m11, m12]
    norm_num [ind, wSigned]

/-- The party score of book two is not faithful. -/
theorem signed_partyScore_not_faithful :
    ¬ FaithfulNonnegDiagonal (tableForm (partyScore wSigned (keepsB mark noJoint)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) := by
  intro h
  obtain ⟨h00, h01, h10, h11⟩ := signed_partyScore_values
  have hz : tableForm (partyScore wSigned (keepsB mark noJoint)) (fun _ => 1) (fun _ => 1) = 0 := by
    simp [tableForm, Fin.sum_univ_two, h00, h01, h10, h11]
  have hx : (fun _ : Fin 2 => (1 : ℝ)) = 0 := h.2 (fun _ => 1) hz
  have h0 := congrFun hx 0
  simp at h0

/-- Same costs for every family; the party score meets K1's typed conditions in one book and not in the
other. -/
theorem same_costs_different_verdicts :
    keptCost wSigned (keepsB mark noJoint) = keptCost w (keepsB mark joint) ∧
      FaithfulNonnegDiagonal (tableForm (partyScore w (keepsB mark joint)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) ∧
      ¬ FaithfulNonnegDiagonal (tableForm (partyScore wSigned (keepsB mark noJoint)))
        (LinearEquiv.refl ℝ (Fin 2 → ℝ)) :=
  ⟨same_costs, partyScore_meets_K1.2, signed_partyScore_not_faithful⟩

end APFPaper5.K1.JointPair


theorem solution :
And
  (@Eq.{1} ((S : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) → Real)
    (@APFPaper5.K1.keptCost.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.JointPair.wSigned
      (@APFPaper5.K1.keepsB.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) APFPaper5.K1.JointPair.mark
        APFPaper5.K1.JointPair.noJoint))
    (@APFPaper5.K1.keptCost.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.JointPair.w
      (@APFPaper5.K1.keepsB.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) APFPaper5.K1.JointPair.mark
        APFPaper5.K1.JointPair.joint)))
  (And
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
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            APFPaper5.K1.JointPair.mark APFPaper5.K1.JointPair.joint)))
      (@LinearEquiv.refl.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
        Real.semiring
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommMonoid)
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
          Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))))
    (Not
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
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) APFPaper5.K1.JointPair.wSigned
            (@APFPaper5.K1.keepsB.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              APFPaper5.K1.JointPair.mark APFPaper5.K1.JointPair.noJoint)))
        (@LinearEquiv.refl.{0, 0} Real (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Real)
          Real.semiring
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) => Real.instAddCommMonoid)
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring)))))) := by
  exact @APFPaper5.K1.JointPair.same_costs_different_verdicts
