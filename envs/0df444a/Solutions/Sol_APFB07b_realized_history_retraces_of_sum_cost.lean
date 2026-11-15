-- Prove2me | solution 1 for APFB07b.realized_history_retraces_of_sum_cost
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:11:03.622204+00:00
-- url     : https://prove2.me/submissions/59cec818-c757-43aa-acd8-a372882a5aec

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB07_realized_history_retraces
title: Under A2 and BW, if total cost is a sum over the moments of a history and the reversed history is admissible, the realized history retraces; if it also moves, two moments have the same present records and, by B01, different physical objects
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B07a (A2), B07b (BW, "Unique minimum"), B01, in their declared Lean forms. The A2
 definition node binds totalCost to "the ORIGINAL total admissibility cost (sum of distinction costs in the
 adopted Paper0 statement)", Paper 0 v6.2.56:3454-3458. The author's ruling of 2026-11-13 adopting the
 relation sentence (RULING_relation_sentence_2026-11-13.md).
consumes_inputs: A2 and BW in declared form; B01 through its descent form in the last two theorems. The
 formal fidelity of A2 is NOT CERTIFIED. The bindings are supplied: the configurations at an interface are
 taken to be histories of present records over a finite set of moments. A supplied instance does not
 certify the physical statement.
statement: T is a finite set of moments, sigma sends a moment to its mirror, next is one step on.
 (sum_cost_direction_blind) a cost that is a sum over the moments is the same for a history and its mirror.
 (APFB07b.realized_history_symmetric) if the mirror of an admissible history is admissible and total cost
 is the same for both, the realized history reads the same at a moment and at its mirror.
 (APFB07b.realized_history_retraces_of_sum_cost) in particular when total cost is a sum over the moments.
 (symmetric_history_same_now_different_next) for a history that reads the same at mirror moments: if the
 record two steps on from a moment differs from the record at it, then the moment one step on and its
 mirror have the same record now and different records one step later.
 (APFB01.distinct_objects_on_symmetric_history) if the history is the record of states under a hold and
 what the records read after the hold is a physical fact, the states at those two moments are different
 physical objects with the same present records.
 (APFB07b.rate_is_held_on_realized_history) all of it in one statement.
 (APFB07b.one_way_history_meets_A2_BW) a supplied instance of A2 and BW with a sum cost whose realized
 history does not retrace and whose present record fixes the next: the mirror history is not admissible
 there. So the clause "the mirror of an admissible history is admissible" is doing work.
reading: "the way back retraces the way out" follows from A2 and BW once holds can be undone and cost is
 a sum. "The rate is held" then follows with B01 once the history moves.
not_claimed: that the mirror of an admissible history is admissible at any interface (this is "a hold can be
 undone"); that the realized history moves; that configurations are record histories; any K.
-/
import Theorems.Thm_APFB07b_realized_fixed_by_cost_symmetry
import Theorems.Thm_APFB07b_realized_has_no_rate_of_present_records
import Theorems.Thm_APFB07b_realized_rate_not_forbidden
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

universe uX uP uR

namespace APFPaper5.K3

theorem sum_cost_direction_blind {T : Type*} [Fintype T] {R : Type*} (sigma : T ≃ T)
    (c : R → ℝ) (r : T → R) : ∑ t, c (r (sigma t)) = ∑ t, c (r t) :=
  Equiv.sum_comp sigma (fun t => c (r t))

theorem symmetric_history_same_now_different_next {T : Type*} {R : Type*} (r : T → R)
    (next sigma : T → T) (hsigma : ∀ t : T, next (sigma (next t)) = sigma t)
    (hsym : ∀ t : T, r (sigma t) = r t) (t : T) (hmove : r (next (next t)) ≠ r t) :
    r (sigma (next t)) = r (next t) ∧ r (next (sigma (next t))) ≠ r (next (next t)) := by
  refine ⟨hsym (next t), ?_⟩
  rw [hsigma, hsym]
  exact fun e => hmove e.symm

end APFPaper5.K3

theorem APFB07b.realized_history_symmetric {Interface : Type*} {T : Type*} {R : Type*}
    (originalAdmissible : Interface → (T → R) → Prop) (totalCost : Interface → (T → R) → ℝ)
    (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (sigma : T → T)
    (hundo : ∀ i r, originalAdmissible i r → originalAdmissible i (fun t => r (sigma t)))
    (hcost : ∀ i r, totalCost i (fun t => r (sigma t)) = totalCost i r) (i : Interface) (t : T) :
    realized i (sigma t) = realized i t :=
  congrFun (APFB07b.realized_fixed_by_cost_symmetry originalAdmissible totalCost realized hA2 hBW i
    (fun r t => r (sigma t)) (hundo i) (hcost i)) t

theorem APFB07b.realized_history_retraces_of_sum_cost {Interface : Type*} {T : Type*} [Fintype T]
    {R : Type*} (originalAdmissible : Interface → (T → R) → Prop)
    (totalCost : Interface → (T → R) → ℝ) (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (sigma : T ≃ T)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (hundo : ∀ i r, originalAdmissible i r → originalAdmissible i (fun t => r (sigma t)))
    (i : Interface) (t : T) : realized i (sigma t) = realized i t :=
  APFB07b.realized_history_symmetric originalAdmissible totalCost realized hA2 hBW sigma hundo
    (fun i r => by
      rw [hsum, hsum]
      exact APFPaper5.K3.sum_cost_direction_blind sigma (c i) r) i t

theorem APFB01.distinct_objects_on_symmetric_history {T : Type*} {X : Type uX} {Process : Type uP}
    {R : Type uR} (profile : X → Process → Prop) (now : X → R) (D : X → X) (o : T → X)
    (next sigma : T → T) (hsigma : ∀ t : T, next (sigma (next t)) = sigma t)
    (ho : ∀ t : T, o (next t) = D (o t)) (hsym : ∀ t : T, now (o (sigma t)) = now (o t))
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => now (D x) = r))
    (t : T) (hmove : now (o (next (next t))) ≠ now (o t)) :
    now (o (sigma (next t))) = now (o (next t)) ∧
      APFB01.physicalClass profile (o (sigma (next t))) ≠
        APFB01.physicalClass profile (o (next t)) := by
  obtain ⟨e1, e2⟩ := APFPaper5.K3.symmetric_history_same_now_different_next
    (fun t => now (o t)) next sigma hsigma hsym t hmove
  refine ⟨e1, APFB01.distinct_objects_of_later_record profile (fun z => now (D z)) hfact _ _ ?_⟩
  show now (D (o (sigma (next t)))) ≠ now (D (o (next t)))
  rw [← ho, ← ho]
  exact e2

theorem APFB07b.rate_is_held_on_realized_history {Interface : Type*} {T : Type*} [Fintype T]
    {X : Type uX} {Process : Type uP} {R : Type uR}
    (originalAdmissible : Interface → (T → R) → Prop) (totalCost : Interface → (T → R) → ℝ)
    (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (sigma : T ≃ T) (next : T → T)
    (hsigma : ∀ t : T, next (sigma (next t)) = sigma t)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (hundo : ∀ i r, originalAdmissible i r → originalAdmissible i (fun t => r (sigma t)))
    (i : Interface) (profile : X → Process → Prop) (now : X → R) (D : X → X) (o : T → X)
    (hrec : ∀ t : T, realized i t = now (o t)) (ho : ∀ t : T, o (next t) = D (o t))
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => now (D x) = r))
    (t : T) (hmove : realized i (next (next t)) ≠ realized i t) :
    now (o (sigma (next t))) = now (o (next t)) ∧
      APFB01.physicalClass profile (o (sigma (next t))) ≠
        APFB01.physicalClass profile (o (next t)) := by
  have hsym : ∀ u : T, now (o (sigma u)) = now (o u) := fun u => by
    rw [← hrec, ← hrec]
    exact APFB07b.realized_history_retraces_of_sum_cost originalAdmissible totalCost realized hA2
      hBW sigma c hsum hundo i u
  exact APFB01.distinct_objects_on_symmetric_history profile now D o next sigma hsigma ho hsym
    hfact t (by rw [← hrec, ← hrec]; exact hmove)

theorem APFB07b.one_way_history_meets_A2_BW :
    ∃ (originalAdmissible : Unit → (Fin 3 → ℝ) → Prop) (totalCost : Unit → (Fin 3 → ℝ) → ℝ)
      (realized : Unit → (Fin 3 → ℝ)),
      APFB07a.A2Selection originalAdmissible totalCost realized ∧
        APFB07b.BWUniqueMinimum originalAdmissible totalCost ∧
        (∀ r, totalCost () r = ∑ t, r t) ∧ realized () 2 ≠ realized () 1 ∧
        ∀ s t : Fin 3, realized () s = realized () t → s = t := by
  refine ⟨fun _ r => r = fun t => (t.val : ℝ), fun _ r => ∑ t, r t, fun _ t => (t.val : ℝ),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨rfl, fun G hG => by rw [hG]⟩
  · intro i
    exact ⟨fun t => (t.val : ℝ), ⟨rfl, fun H hH => by rw [hH]⟩, fun H hH => hH.1⟩
  · intro r
    rfl
  · show ((2 : ℕ) : ℝ) ≠ ((1 : ℕ) : ℝ)
    norm_num
  · intro s t e
    have e' : ((s.val : ℕ) : ℝ) = ((t.val : ℕ) : ℝ) := e
    exact Fin.ext (Nat.cast_injective e')


universe apfNative_u_1 apfNative_u_2 apfNative_u_3
theorem solution :
∀ {Interface : Type apfNative_u_1} {T : Type apfNative_u_2} [inst : Fintype.{apfNative_u_2} T] {R : Type apfNative_u_3}
  (originalAdmissible : Interface → (T → R) → Prop) (totalCost : Interface → (T → R) → Real)
  (realized : Interface → T → R)
  (hA2 :
    @APFB07a.A2Selection.{apfNative_u_1, max apfNative_u_2 apfNative_u_3} Interface (fun (i : Interface) => T → R)
      originalAdmissible totalCost realized)
  (hBW :
    @APFB07b.BWUniqueMinimum.{apfNative_u_1, max apfNative_u_2 apfNative_u_3} Interface (fun (i : Interface) => T → R)
      originalAdmissible totalCost)
  (sigma : Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) (c : Interface → R → Real)
  (hsum :
    ∀ (i : Interface) (r : T → R),
      @Eq.{1} Real (totalCost i r)
        (@Finset.sum.{apfNative_u_2, 0} T Real Real.instAddCommMonoid (@Finset.univ.{apfNative_u_2} T inst)
          fun (t : T) => c i (r t)))
  (hundo :
    ∀ (i : Interface) (r : T → R),
      originalAdmissible i r →
        originalAdmissible i fun (t : T) =>
          r
            (@DFunLike.coe.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
              (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T (fun (x : T) => T)
              (@EquivLike.toFunLike.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
                (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T T
                (@Equiv.instEquivLike.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T))
              sigma t))
  (i : Interface) (t : T),
  @Eq.{apfNative_u_3 + 1} R
    (realized i
      (@DFunLike.coe.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
        (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T (fun (x : T) => T)
        (@EquivLike.toFunLike.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
          (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T T
          (@Equiv.instEquivLike.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T))
        sigma t))
    (realized i t) := by
  exact @APFB07b.realized_history_retraces_of_sum_cost
