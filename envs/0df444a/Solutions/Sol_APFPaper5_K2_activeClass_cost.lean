-- Prove2me | solution 1 for APFPaper5.K2.activeClass_cost
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:30:10.208587+00:00
-- url     : https://prove2.me/submissions/a61304e4-8de0-4c25-9519-506b3f986601

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-15; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K2_state_class_candidates
title: What each candidate for "what a state holds" costs: under holds, under a turn-over, and in the cost it gives what is held
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: TEE_UP_K2_what_a_state_holds_2026-11-15; Def_APFPaper5_K2_StateClass (the three candidates); Def_APFPaper5_K2_HoldScore (RearrangesFamily, heldAfter); the builder seat's
 Def_APFPaper5_K1_MarkTable and Def_APFPaper5_K1_PartyScore.
standing: EVIDENCE put to the author before the ruling of 2026-11-15 13:54 HST, which took C for what is
 recorded (RULING_C_for_what_is_recorded_2026-11-15). A and B were not chosen. Every statement is ordinary
 mathematics on the typed candidates and is unchanged by the ruling.
consumes_inputs: none.
theorems:
 - (atomTable_eq_recordForm, tableForm_atomTable_eq_recordForm) K1's table is the weighted overlap of the
   distinctions' record lists, and K1's form of two classes of distinctions is the weighted overlap of the
   classes of records they stand for.
 - Candidate A.
   (activeClass_after_hold_of_no_turn) under a hold that turns nothing over, what the state holds after the
   hold is what the hold makes of what it held.
   (activeClass_after_turn) on a distinction the hold turns over, it is one minus that. Not linear.
   (activeClass_cost) the cost K1's form gives the class is, record by record, the record's cost times the
   square of the number of true distinctions listed against it.
   (shared_record_counts_four) two distinctions listed against one record of cost 1, both true: the class
   costs 4. The family keeps one record of cost 1.
 - Candidate B.
   (sideClass_after_hold) under any hold, turn-overs included, the class after the hold is what the hold
   makes of the class before, with a change of sign on each distinction turned over. Linear.
   (opposite_sides_cancel) two distinctions listed against one record of cost 1, on opposite sides: the class
   is not zero and costs 0.
 - Candidate C.
   (keptClass_cost) the weighted overlap of the class with itself is the cost of the records the family
   keeps: the ledger's cost of what is held, exactly.
   (keptClass_union_of_disjoint) for a keeping rule that keeps a record for a union exactly when it keeps
   it for one of the two, and two families that keep no record in common, the class of the union is the
   sum of the two classes.
not claimed: that A or B is what a state holds. Anything about what a state holds that is not recorded. That
 a turn-over is or is not to be seen. Anything about tests. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper5_K2_StateClass
import Definitions.Def_APFPaper5_K2_HoldScore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2

universe uI uX uD uW
variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}

theorem ind_mul_self (b : Bool) : ind b * ind b = ind b := by
  cases b <;> simp [ind]

theorem ind_xor_true (b : Bool) : ind (xor true b) = 1 - ind b := by
  cases b <;> simp [ind]

/-! ### K1's table is an overlap of record lists -/

theorem atomTable_eq_recordForm [Fintype W] (w : W → ℝ) (mark : ι → W → Bool) (i j : ι) :
    atomTable w mark i j = recordForm w (partyClass mark i) (partyClass mark j) := rfl

theorem tableForm_atomTable_eq_recordForm [Fintype ι] [Fintype W] (w : W → ℝ)
    (mark : ι → W → Bool) (x y : ι → ℝ) :
    tableForm (atomTable w mark) x y = recordForm w (markLift mark x) (markLift mark y) := by
  have h1 : ∀ a, w a * ((∑ i, x i * ind (mark i a)) * (∑ j, y j * ind (mark j a))) =
      ∑ i, ∑ j, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j := by
    intro a
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have h2 : ∀ i j, x i * (∑ a, w a * (ind (mark i a) * ind (mark j a))) * y j =
      ∑ a, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j := by
    intro i j
    rw [Finset.mul_sum, Finset.sum_mul]
  show (∑ i, ∑ j, x i * (∑ a, w a * (ind (mark i a) * ind (mark j a))) * y j) =
    ∑ a, w a * ((∑ i, x i * ind (mark i a)) * (∑ j, y j * ind (mark j a)))
  simp only [h1, h2]
  calc (∑ i, ∑ j, ∑ a, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j)
      = ∑ i, ∑ a, ∑ j, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ a, ∑ i, ∑ j, x i * (w a * (ind (mark i a) * ind (mark j a))) * y j := Finset.sum_comm

/-! ### Candidate A: the distinctions that read true, added up -/

theorem activeClass_after_hold_of_no_turn (reads : D → X → Bool) (dist : ι → D) (h : X → X)
    (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
    (hno : ∀ i, flip i = false) (x : X) :
    activeClass reads dist (h x) = heldAfter sigma (activeClass reads dist x) := by
  funext i
  show ind (reads (dist i) (h x)) = ind (reads (dist (sigma i)) x)
  rw [r i x, hno i, Bool.false_xor]

theorem activeClass_after_turn (reads : D → X → Bool) (dist : ι → D) (h : X → X)
    (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
    (i : ι) (hi : flip i = true) (x : X) :
    activeClass reads dist (h x) i = 1 - heldAfter sigma (activeClass reads dist x) i := by
  show ind (reads (dist i) (h x)) = 1 - ind (reads (dist (sigma i)) x)
  rw [r i x, hi, ind_xor_true]

/-- The cost K1's form gives the class: record by record, the record's cost times the square of the number
of true distinctions listed against it. -/
theorem activeClass_cost [Fintype ι] [Fintype W] (w : W → ℝ) (mark : ι → W → Bool)
    (reads : D → X → Bool) (dist : ι → D) (x : X) :
    tableForm (atomTable w mark) (activeClass reads dist x) (activeClass reads dist x) =
      ∑ a, w a * ((∑ i, ind (reads (dist i) x) * ind (mark i a)) *
        (∑ i, ind (reads (dist i) x) * ind (mark i a))) :=
  tableForm_atomTable_eq_recordForm w mark _ _

/-- Two distinctions listed against one record of cost 1, both true: the class costs 4. -/
theorem shared_record_counts_four :
    tableForm (atomTable (fun _ : Unit => (1 : ℝ)) (fun (_ : Bool) (_ : Unit) => true))
      (fun _ => 1) (fun _ => 1) = 4 := by
  rw [tableForm_atomTable_eq_recordForm]
  simp [recordForm, markLift, ind]
  norm_num

/-! ### Candidate B: the side of each distinction -/

theorem sideClass_after_hold (reads : D → X → Bool) (dist : ι → D) (h : X → X)
    (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
    (i : ι) (x : X) :
    sideClass reads dist (h x) i =
      (if flip i then (-1 : ℝ) else 1) * heldAfter sigma (sideClass reads dist x) i := by
  show (if reads (dist i) (h x) then (1 : ℝ) else -1) =
    (if flip i then (-1 : ℝ) else 1) * (if reads (dist (sigma i)) x then (1 : ℝ) else -1)
  rw [r i x]
  cases flip i <;> cases reads (dist (sigma i)) x <;> simp

/-- Two distinctions listed against one record of cost 1, on opposite sides: the class is not zero and
costs 0. -/
theorem opposite_sides_cancel :
    tableForm (atomTable (fun _ : Unit => (1 : ℝ)) (fun (_ : Bool) (_ : Unit) => true))
      (fun b : Bool => if b then 1 else -1) (fun b : Bool => if b then 1 else -1) = 0 := by
  rw [tableForm_atomTable_eq_recordForm]
  simp [recordForm, markLift, ind]

/-! ### Candidate C: the records the held family keeps -/

/-- The weighted overlap of the class with itself is the cost of the records the family keeps. -/
theorem keptClass_cost [Fintype W] (w : W → ℝ) (keeps : Finset D → W → Bool) (S : Finset D) :
    recordForm w (keptClass keeps S) (keptClass keeps S) = keptCost w keeps S := by
  unfold recordForm keptClass keptCost
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ind_mul_self]

/-- Where a union keeps a record exactly when one of the two families does, and the two keep no record in
common, the class of the union is the sum of the two classes. -/
theorem keptClass_union_of_disjoint [DecidableEq D] (keeps : Finset D → W → Bool)
    (S T : Finset D) (hunion : ∀ a, keeps (S ∪ T) a = (keeps S a || keeps T a))
    (hdisj : ∀ a, ¬ (keeps S a = true ∧ keeps T a = true)) :
    keptClass keeps (S ∪ T) = keptClass keeps S + keptClass keeps T := by
  funext a
  show ind (keeps (S ∪ T) a) = ind (keeps S a) + ind (keeps T a)
  rw [hunion a]
  have hd := hdisj a
  cases hS : keeps S a <;> cases hT : keeps T a <;> simp [ind, hS, hT] at hd ⊢

end APFPaper5.K2


universe apfNative_uI apfNative_uX apfNative_uD apfNative_uW
theorem solution :
∀ {ι : Type apfNative_uI} {X : Type apfNative_uX} {D : Type apfNative_uD} {W : Type apfNative_uW}
  [inst : Fintype.{apfNative_uI} ι] [inst_1 : Fintype.{apfNative_uW} W] (w : W → Real) (mark : ι → W → Bool)
  (reads : D → X → Bool) (dist : ι → D) (x : X),
  @Eq.{1} Real
    (@APFPaper5.K1.tableForm.{apfNative_uI} ι inst
      (@APFPaper5.K1.atomTable.{apfNative_uI, apfNative_uW} ι W inst_1 w mark)
      (@APFPaper5.K2.activeClass.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist x)
      (@APFPaper5.K2.activeClass.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist x))
    (@Finset.sum.{apfNative_uW, 0} W Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uW} W inst_1) fun (a : W) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (w a)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Finset.sum.{apfNative_uI, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uI} ι inst)
            fun (i : ι) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (APFPaper5.K1.ind (reads (dist i) x))
              (APFPaper5.K1.ind (mark i a)))
          (@Finset.sum.{apfNative_uI, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uI} ι inst)
            fun (i : ι) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (APFPaper5.K1.ind (reads (dist i) x))
              (APFPaper5.K1.ind (mark i a))))) := by
  exact @APFPaper5.K2.activeClass_cost
