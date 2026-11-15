-- Prove2me | solution 1 for APFPaper5.K3.commonTurn_firstOrder
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:03:49.783689+00:00
-- url     : https://prove2.me/submissions/3817ce03-b42d-4cbb-be24-85437c1e8a4f

import Theorems.Thm_APFPaper5_K3_relativeTurn_rotates_cross
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_firstOrder_scope
title: Where the first-order relation holds on the carrier: for the common turn at every held state, for the number and rate of a relation under a turn of one component, and not for a turn of one component at every held state
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: ruling of 2026-11-12 naming the first-order clause ("a held relation is fixed by its present number and
 its rate"; Def_APFPaper5_K3_FirstOrder). Controls for the decision put to the author on 2026-11-13.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
statement: (commonTurn_firstOrder) for the common turn by a unit pair, the second turn of a held state is a
 combination of the state and its first turn, at every held state.
 (relation_firstOrder) under a turn of one component by a unit pair, the number and the rate of the relation
 between the two components each obey the same relation.
 (relativeTurn_breaks_firstOrder_for_states) for a quarter turn of one component there is a held state at
 which the second turn is no combination of the state and its first turn.
reading: the clause cannot be read as "every admitted turn, at every held state". It holds for the common
 turn of a held state and for the number and rate of a relation.
not_claimed: which reading the author intends; any K.
-/
import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_commonTurn_unseen
import Theorems.Thm_APFPaper5_K3_records_are_cross_data
import Theorems.Thm_APFPaper5_K3_commonQuarter_commutes_common
import Theorems.Thm_APFPaper5_K3_same_records_give_common_turn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

theorem commonTurn_firstOrder (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    commonTurn c s (commonTurn c s h) =
      add2 (smul2 (-1) h) (smul2 (2 * c) (commonTurn c s h)) := by
  have e : commonTurn c s (commonTurn c s h) =
      add2 (smul2 (-(c * c + s * s)) h) (smul2 (2 * c) (commonTurn c s h)) := by
    apply Held2.ext <;> dsimp only [commonTurn, add2, smul2] <;> ring
  rw [hcs] at e
  exact e

theorem relation_firstOrder (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    crossRe (relativeTurn c s (relativeTurn c s h)) =
        -crossRe h + 2 * c * crossRe (relativeTurn c s h) ∧
      crossIm (relativeTurn c s (relativeTurn c s h)) =
        -crossIm h + 2 * c * crossIm (relativeTurn c s h) := by
  obtain ⟨r1, i1⟩ := relativeTurn_rotates_cross c s (relativeTurn c s h)
  obtain ⟨r0, i0⟩ := relativeTurn_rotates_cross c s h
  constructor
  · rw [r1, r0, i0]
    linear_combination (-crossRe h) * hcs
  · rw [i1, r0, i0]
    linear_combination (-crossIm h) * hcs

theorem relativeTurn_breaks_firstOrder_for_states :
    ¬ ∃ α β : ℝ, relativeTurn 0 1 (relativeTurn 0 1 ⟨1, 0, 1, 0⟩) =
      add2 (smul2 α ⟨1, 0, 1, 0⟩) (smul2 β (relativeTurn 0 1 ⟨1, 0, 1, 0⟩)) := by
  rintro ⟨α, β, h⟩
  have h1 := congrArg Held2.a1 h
  have h3 := congrArg Held2.b1 h
  have h4 := congrArg Held2.b2 h
  dsimp only [relativeTurn, add2, smul2] at h1 h3 h4
  linarith

end APFPaper5.K3


theorem solution :
∀ (c s : Real)
  (hcs :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c c)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s s))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (h : APFPaper5.K3.Held2),
  @Eq.{1} APFPaper5.K3.Held2 (APFPaper5.K3.commonTurn c s (APFPaper5.K3.commonTurn c s h))
    (APFPaper5.K3.add2
      (APFPaper5.K3.smul2
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) h)
      (APFPaper5.K3.smul2
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          c)
        (APFPaper5.K3.commonTurn c s h))) := by
  exact @APFPaper5.K3.commonTurn_firstOrder
