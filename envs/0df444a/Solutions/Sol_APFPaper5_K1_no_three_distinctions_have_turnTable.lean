-- Prove2me | solution 1 for APFPaper5.K1.no_three_distinctions_have_turnTable
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:55:01.403745+00:00
-- url     : https://prove2.me/submissions/c6df929b-7b9e-4fce-a51d-5bcca4c405d7

import Definitions.Def_APFPaper5_K1_record_tables_and_turns_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_record_tables_and_turns
title: Every table of a record ledger obeys a three-distinction bound; the table of a mark, its turn and its double turn breaks it for every turn strictly between none and the quarter turn; that table is on K1's classes all the same, as combinations that are not record lists
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-15 13:41 HST: "Let's take a harder look at C - quantum implications match?
 Gauge?" (NOTE_harder_look_at_C_quantum_and_gauge_2026-11-15). The builder seat's Def_APFPaper5_K1_MarkTable
 (atomTable: the table read off weights on the atoms of a record space), Thm_APFPaper5_K1_rank_three (the
 score between a mark and its turn is (1 + x) / 2) and its finding that a turn round obeys the rule for a
 turn taken twice (c to 2c^2 - 1) only for no turn or the quarter turn. This seat's
 Def_APFPaper5_K1_SourcePartyScore (the ruled score on source data).
standing: ordinary mathematics on the typed tables. The turn table is a SUPPLIED table of three numbers; that
 a physical turn has it is the builder seat's conditional result and standard quantum theory, not a result
 of this file.
consumes_inputs: none.
theorems:
 - (atomTable_triangle) for a record ledger with no negative cost and any three distinctions i, j, k: the
   score of i with j, plus the score of i with k, minus the score of j with k, is at most the score of i
   with itself. (atomTable_le_diag) the score of two is at most the score of either with itself.
 - (sourcePartyScore_triangle) the ruled score on source data of the declared forms obeys it.
 - (turnTable entries, turnTable_symm) the turn table: index 1 a mark, 0 the mark turned once, 2 the mark
   turned twice; unit diagonal; (1 + x) / 2 between neighbours; x * x between the ends.
 - (turnTable_breaks_triangle) for 0 < x < 1 the turn table breaks the bound at the middle index.
 - (no_record_ledger_has_turnTable, no_three_distinctions_have_turnTable) so no record ledger with no
   negative cost has the turn table, and no three distinctions have it as their ruled score.
 - (turnTable_half_form, turnTable_half_nonneg, turnTable_half_faithful) at x = 1/2 (3/4, 3/4, 1/4) the
   turn table is symmetric with a faithful nonnegative diagonal: it meets what K1 asks of a table.
 - (ownTable_eq, turnTable_on_classes) and it is the table of three CLASSES of a record ledger: three
   distinctions with one own record each, of costs 1, 7/16 and 3/14, and the combinations d0,
   3/4 d0 + d1, 3/4 d0 - 5/7 d1 + d2. (turnClass_negative) the third has a negative coefficient.
reading: a turn strictly between none and the quarter turn cannot carry a distinction to a distinction with
 the record ledger's score kept. The numbers a turn needs are in K1's space of classes, on combinations that
 are not lists of records.
not claimed: that any hold is such a turn. That the combinations are states, preparations or tests. Anything
 about which combinations exist. No lane. No claim that the transfer is forced, that the carrier gap is
 closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K1_MarkTable
import Definitions.Def_APFPaper5_K1_SourcePartyScore
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

universe uI uW

/-! ### Every table of a record ledger obeys a three-distinction bound -/

theorem atomTable_triangle {ι : Type uI} {W : Type uW} [Fintype W] (w : W → ℝ)
    (hw : ∀ a, 0 ≤ w a) (mark : ι → W → Bool) (i j k : ι) :
    atomTable w mark i j + atomTable w mark i k - atomTable w mark j k ≤ atomTable w mark i i := by
  unfold atomTable
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have h := hw a
  cases mark i a <;> cases mark j a <;> cases mark k a
  all_goals simp [ind]
  all_goals linarith

theorem atomTable_le_diag {ι : Type uI} {W : Type uW} [Fintype W] (w : W → ℝ)
    (hw : ∀ a, 0 ≤ w a) (mark : ι → W → Bool) (i j : ι) :
    atomTable w mark i j ≤ atomTable w mark i i := by
  unfold atomTable
  refine Finset.sum_le_sum (fun a _ => ?_)
  have h := hw a
  cases mark i a <;> cases mark j a
  all_goals simp [ind]
  all_goals linarith

/-- The ruled score on source data obeys the bound. -/
theorem sourcePartyScore_triangle {D P Record : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq D] [Fintype Record] (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (dist : ι → D) (i j k : ι) :
    sourcePartyScore w maintained sufficient usesToRealize dist i j +
        sourcePartyScore w maintained sufficient usesToRealize dist i k -
        sourcePartyScore w maintained sufficient usesToRealize dist j k ≤
      sourcePartyScore w maintained sufficient usesToRealize dist i i :=
  atomTable_triangle w hw (partyMark (sourceKeeps maintained sufficient usesToRealize dist)) i j k

/-! ### The table of a mark, its turn and its double turn -/



theorem turnTable_diag (x : ℝ) (i : Fin 3) : turnTable x i i = 1 := by
  show (if i = i then (1 : ℝ) else if i = 0 ∨ i = 0 then (1 + x) / 2 else x * x) = 1
  rw [if_pos rfl]

theorem turnTable_01 (x : ℝ) : turnTable x 0 1 = (1 + x) / 2 := by
  show (if (0 : Fin 3) = 1 then (1 : ℝ) else if (0 : Fin 3) = 0 ∨ (1 : Fin 3) = 0 then (1 + x) / 2
    else x * x) = (1 + x) / 2
  rw [if_neg (by decide), if_pos (by decide)]

theorem turnTable_02 (x : ℝ) : turnTable x 0 2 = (1 + x) / 2 := by
  show (if (0 : Fin 3) = 2 then (1 : ℝ) else if (0 : Fin 3) = 0 ∨ (2 : Fin 3) = 0 then (1 + x) / 2
    else x * x) = (1 + x) / 2
  rw [if_neg (by decide), if_pos (by decide)]

theorem turnTable_12 (x : ℝ) : turnTable x 1 2 = x * x := by
  show (if (1 : Fin 3) = 2 then (1 : ℝ) else if (1 : Fin 3) = 0 ∨ (2 : Fin 3) = 0 then (1 + x) / 2
    else x * x) = x * x
  rw [if_neg (by decide), if_neg (by decide)]

theorem turnTable_symm (x : ℝ) (i j : Fin 3) : turnTable x i j = turnTable x j i := by
  show (if i = j then (1 : ℝ) else if i = 0 ∨ j = 0 then (1 + x) / 2 else x * x) =
    (if j = i then (1 : ℝ) else if j = 0 ∨ i = 0 then (1 + x) / 2 else x * x)
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (show ¬ j = i from fun h' => h h'.symm)]
    by_cases h2 : i = 0 ∨ j = 0
    · rw [if_pos h2, if_pos (show j = 0 ∨ i = 0 from h2.symm)]
    · rw [if_neg h2, if_neg (show ¬ (j = 0 ∨ i = 0) from fun h' => h2 h'.symm)]

/-- For a turn strictly between none (x = 1) and the quarter turn (x = 0) the turn table breaks the bound at
the mark turned once. -/
theorem turnTable_breaks_triangle (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    turnTable x 0 0 < turnTable x 0 1 + turnTable x 0 2 - turnTable x 1 2 := by
  rw [turnTable_diag, turnTable_01, turnTable_02, turnTable_12]
  nlinarith

/-- No record ledger with no negative cost has the turn table. -/
theorem no_record_ledger_has_turnTable {W : Type uW} [Fintype W] (w : W → ℝ) (hw : ∀ a, 0 ≤ w a)
    (mark : Fin 3 → W → Bool) (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    ¬ ∀ i j, atomTable w mark i j = turnTable x i j := by
  intro h
  have t := atomTable_triangle w hw mark 0 1 2
  rw [h 0 1, h 0 2, h 1 2, h 0 0] at t
  exact absurd t (not_le.mpr (turnTable_breaks_triangle x h0 h1))

/-- No three distinctions have the turn table as their ruled score. -/
theorem no_three_distinctions_have_turnTable {D P Record : Type*} [DecidableEq D] [Fintype Record]
    (w : Record → ℝ) (hw : ∀ a, 0 ≤ w a) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (dist : Fin 3 → D) (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    ¬ ∀ i j, sourcePartyScore w maintained sufficient usesToRealize dist i j = turnTable x i j :=
  no_record_ledger_has_turnTable w hw
    (partyMark (sourceKeeps maintained sufficient usesToRealize dist)) x h0 h1

/-! ### At x = 1/2 the turn table meets what K1 asks of a table -/

theorem turnTable_half_form (u v : Fin 3 → ℝ) :
    tableForm (turnTable (1 / 2)) u v =
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 +
        3 / 4 * (u 0 * v 1 + u 1 * v 0 + u 0 * v 2 + u 2 * v 0) +
        1 / 4 * (u 1 * v 2 + u 2 * v 1) := by
  unfold tableForm
  simp only [Fin.sum_univ_three]
  rw [turnTable_diag, turnTable_diag, turnTable_diag, turnTable_symm (1 / 2) 1 0,
    turnTable_symm (1 / 2) 2 0, turnTable_symm (1 / 2) 2 1, turnTable_01, turnTable_02,
    turnTable_12]
  ring

theorem turnTable_half_nonneg (u : Fin 3 → ℝ) : 0 ≤ tableForm (turnTable (1 / 2)) u u := by
  rw [turnTable_half_form]
  nlinarith [mul_self_nonneg (u 0 + 3 / 4 * u 1 + 3 / 4 * u 2),
    mul_self_nonneg (u 1 - 5 / 7 * u 2), mul_self_nonneg (u 2)]

theorem turnTable_half_faithful (u : Fin 3 → ℝ) (h : tableForm (turnTable (1 / 2)) u u = 0) :
    u = 0 := by
  rw [turnTable_half_form] at h
  have hA := mul_self_nonneg (u 0 + 3 / 4 * u 1 + 3 / 4 * u 2)
  have hB := mul_self_nonneg (u 1 - 5 / 7 * u 2)
  have hC := mul_self_nonneg (u 2)
  have h2 : u 2 * u 2 = 0 := by nlinarith
  have hu2 : u 2 = 0 := mul_self_eq_zero.mp h2
  have hB2 : (u 1 - 5 / 7 * u 2) * (u 1 - 5 / 7 * u 2) = 0 := by nlinarith
  have hu1 : u 1 = 0 := by
    have e := mul_self_eq_zero.mp hB2
    rw [hu2] at e
    linarith
  have hA2 : (u 0 + 3 / 4 * u 1 + 3 / 4 * u 2) * (u 0 + 3 / 4 * u 1 + 3 / 4 * u 2) = 0 := by
    nlinarith
  have hu0 : u 0 = 0 := by
    have e := mul_self_eq_zero.mp hA2
    rw [hu1, hu2] at e
    linarith
  funext i
  fin_cases i
  · exact hu0
  · exact hu1
  · exact hu2

/-! ### The turn table on the classes of a record ledger -/







theorem ownTable_eq (i j : Fin 3) :
    atomTable ownCost ownMark i j = if i = j then ownCost i else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [atomTable, ownCost, ownMark, ind]

theorem turnClass_negative : turnClass 2 1 < 0 := by
  show (if (2 : Fin 3) = 0 then (if (1 : Fin 3) = 0 then (1 : ℝ) else 0)
    else if (2 : Fin 3) = 1 then (if (1 : Fin 3) = 0 then 3 / 4 else if (1 : Fin 3) = 1 then 1 else 0)
    else (if (1 : Fin 3) = 0 then 3 / 4 else if (1 : Fin 3) = 1 then -(5 / 7) else 1)) < 0
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  norm_num

/-- The turn table at x = 1/2 is the table of the three classes, for the record ledger above. -/
theorem turnTable_on_classes (k l : Fin 3) :
    tableForm (atomTable ownCost ownMark) (turnClass k) (turnClass l) = turnTable (1 / 2) k l := by
  unfold tableForm
  simp only [ownTable_eq, Fin.sum_univ_three]
  fin_cases k <;> fin_cases l <;>
    simp [ownCost, turnClass, turnTable] <;> norm_num

end APFPaper5.K1


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_3}
  [inst : DecidableEq.{apfNative_u_1 + 1} D] [inst_1 : Fintype.{apfNative_u_3} Record] (w : Record → Real)
  (hw :
    ∀ (a : Record),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w a))
  (maintained : P → Set.{apfNative_u_3} Record) (sufficient : P → Set.{apfNative_u_3} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_3} Record → Prop)
  (dist : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → D) (x : Real)
  (h0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) x)
  (h1 : @LT.lt.{0} Real Real.instLT x (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  Not
    (∀ (i j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
      @Eq.{1} Real
        (@APFPaper5.K1.sourcePartyScore.{apfNative_u_1, apfNative_u_2, apfNative_u_3, 0} D P Record
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) inst inst_1 w maintained
          sufficient usesToRealize dist i j)
        (APFPaper5.K1.turnTable x i j)) := by
  exact @APFPaper5.K1.no_three_distinctions_have_turnTable
