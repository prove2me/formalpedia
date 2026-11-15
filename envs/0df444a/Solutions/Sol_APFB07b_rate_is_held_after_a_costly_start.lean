-- Prove2me | solution 1 for APFB07b.rate_is_held_after_a_costly_start
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:14:52.435548+00:00
-- url     : https://prove2.me/submissions/39459dab-60cc-42dc-ba94-242b9bd8cb6b

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB07_moves
title: "Moves" from both sides: the adopted continuity clause gives plain motion but not the form the rate needs; under A2 a history with no marked moment does not move, and a history held at one moment away from the cheapest record moves off it, which with BW and B01 gives the rate
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's direction of 2026-11-13 15:56 HST ("2": go after "moves" from both sides).
 Def_APFPaper5_K3_Continuity (the continuity clause adopted 2026-11-12). FOUNDATION_INPUTS B07a (A2), B07b
 (BW), B01 in declared form. Thm_APFB07_realized_history_retraces.
consumes_inputs: A2 in the theorems named APFB07a and APFB07b; BW in those named APFB07b; B01 through its
 descent form in the last. The formal fidelity of A2 is NOT CERTIFIED. Bindings are supplied: configurations
 are histories of present records over finitely many moments; total cost is a sum over the moments; the
 admissible histories are exactly those with a given record at a marked moment.
statement: (moves_of_continuity) under the adopted continuity clause, from every held state some admissible
 turn changes the relation.
 (continuity_met_by_self_undoing_turns) the clause is met by a supplied model in which every admissible
 turn, done twice, returns every state. So the clause does not give a hold whose record two steps on differs
 from its record now, which is the form the rate proof uses.
 (APFB07b.realized_history_static_of_shift) A2 and BW: if the shifted history of an admissible history is
 admissible and total cost is a sum over the moments, the realized history reads the same at every step.
 With no marked moment nothing moves.
 (APFB07a.realized_moves_off_a_costly_start) A2: if the admissible histories are those with a given record
 at a marked moment, and some record is cheaper than that one, then at every other moment the realized
 history holds a cheaper record than at the marked moment. It moves off the start.
 (APFB07b.rate_is_held_after_a_costly_start) with BW and B01: if also the mirror fixes the marked moment and
 two steps on from it is a different moment, then the moment after the marked one and its mirror have the
 same present records and are different physical objects.
reading: the named part "moves" can be traded for "at some moment the occupant holds a record that is not
 the cheapest". A2 then moves it.
not_claimed: that any interface has a marked moment or a start that is not the cheapest; that the motion is
 gradual (with a cost that is a plain sum over moments the realized history leaves the start in one step);
 any K.
-/
import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFB07b_realized_history_retraces_of_sum_cost
import Theorems.Thm_APFB07b_rate_is_held_on_realized_history
import Theorems.Thm_APFB07b_one_way_history_meets_A2_BW
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false

universe uX uP uR

namespace APFPaper5.K3

theorem moves_of_continuity {S : Type*} (rel : S → ℝ) (lo hi : ℝ) (Adm : Set (S → S))
    (hc : Continuity rel lo hi Adm) (s : S) : ∃ f ∈ Adm, rel (f s) ≠ rel s := by
  obtain ⟨⟨hlt, _⟩, hreach, _⟩ := hc
  by_cases h : rel s = lo
  · obtain ⟨f, hf, e⟩ := hreach s hi (le_of_lt hlt) (le_refl _)
    exact ⟨f, hf, by rw [e, h]; exact hlt.ne'⟩
  · obtain ⟨f, hf, e⟩ := hreach s lo (le_refl _) (le_of_lt hlt)
    exact ⟨f, hf, by rw [e]; exact fun h' => h h'.symm⟩

theorem continuity_met_by_self_undoing_turns :
    Continuity (fun s : ℝ => s) 0 1 {f : ℝ → ℝ | ∃ a b : ℝ, f = fun s => Equiv.swap a b s} ∧
      ∀ f ∈ {f : ℝ → ℝ | ∃ a b : ℝ, f = fun s => Equiv.swap a b s}, ∀ s : ℝ, f (f s) = s := by
  refine ⟨⟨⟨by norm_num, fun t _ _ => ⟨t, rfl⟩⟩, ?_, ?_⟩, ?_⟩
  · intro s t _ _
    exact ⟨fun x => Equiv.swap s t x, ⟨s, t, rfl⟩, Equiv.swap_apply_left s t⟩
  · rintro f ⟨a, b, rfl⟩
    exact ⟨fun x => Equiv.swap a b x, ⟨a, b, rfl⟩, fun s => Equiv.swap_apply_self a b s⟩
  · rintro f ⟨a, b, rfl⟩ s
    exact Equiv.swap_apply_self a b s

end APFPaper5.K3

theorem APFB07b.realized_history_static_of_shift {Interface : Type*} {T : Type*} [Fintype T]
    {R : Type*} (originalAdmissible : Interface → (T → R) → Prop)
    (totalCost : Interface → (T → R) → ℝ) (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (next : T ≃ T)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (hshift : ∀ i r, originalAdmissible i r → originalAdmissible i (fun t => r (next t)))
    (i : Interface) (t : T) : realized i (next t) = realized i t :=
  APFB07b.realized_history_retraces_of_sum_cost originalAdmissible totalCost realized hA2 hBW next c
    hsum hshift i t

theorem APFB07a.realized_moves_off_a_costly_start {Interface : Type*} {T : Type*} [Fintype T]
    [DecidableEq T] {R : Type*} (originalAdmissible : Interface → (T → R) → Prop)
    (totalCost : Interface → (T → R) → ℝ) (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (t0 : Interface → T) (e : Interface → R)
    (hadm : ∀ i r, originalAdmissible i r ↔ r (t0 i) = e i)
    (i : Interface) (v : R) (hv : c i v < c i (e i)) (t : T) (ht : t ≠ t0 i) :
    realized i (t0 i) = e i ∧ c i (realized i t) < c i (e i) := by
  have h0 : realized i (t0 i) = e i := (hadm i _).mp (hA2 i).1
  refine ⟨h0, ?_⟩
  by_contra hnot
  have hge : c i (e i) ≤ c i (realized i t) := not_lt.mp hnot
  have hG : originalAdmissible i (fun s => if s = t then v else realized i s) := by
    rw [hadm]
    show (if t0 i = t then v else realized i (t0 i)) = e i
    rw [if_neg (fun h => ht h.symm), h0]
  have hle := (hA2 i).2 _ hG
  rw [hsum, hsum] at hle
  have hlt : ∑ s, c i (if s = t then v else realized i s) < ∑ s, c i (realized i s) := by
    apply Finset.sum_lt_sum
    · intro s _
      by_cases hs : s = t
      · rw [if_pos hs, hs]
        exact le_of_lt (lt_of_lt_of_le hv hge)
      · rw [if_neg hs]
    · exact ⟨t, Finset.mem_univ t, by rw [if_pos rfl]; exact lt_of_lt_of_le hv hge⟩
  exact absurd hle (not_le.mpr hlt)

theorem APFB07b.rate_is_held_after_a_costly_start {Interface : Type*} {T : Type*} [Fintype T]
    [DecidableEq T] {X : Type uX} {Process : Type uP} {R : Type uR}
    (originalAdmissible : Interface → (T → R) → Prop) (totalCost : Interface → (T → R) → ℝ)
    (realized : Interface → (T → R))
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (sigma : T ≃ T) (next : T → T)
    (hsigma : ∀ t : T, next (sigma (next t)) = sigma t)
    (c : Interface → R → ℝ) (hsum : ∀ i r, totalCost i r = ∑ t, c i (r t))
    (t0 : Interface → T) (e : Interface → R)
    (hadm : ∀ i r, originalAdmissible i r ↔ r (t0 i) = e i)
    (hfix : ∀ i, sigma (t0 i) = t0 i)
    (i : Interface) (v : R) (hv : c i v < c i (e i)) (h3 : next (next (t0 i)) ≠ t0 i)
    (profile : X → Process → Prop) (now : X → R) (D : X → X) (o : T → X)
    (hrec : ∀ t : T, realized i t = now (o t)) (ho : ∀ t : T, o (next t) = D (o t))
    (hfact : ∀ r : R, APFB01.Descends profile (fun x => now (D x) = r)) :
    now (o (sigma (next (t0 i)))) = now (o (next (t0 i))) ∧
      APFB01.physicalClass profile (o (sigma (next (t0 i)))) ≠
        APFB01.physicalClass profile (o (next (t0 i))) := by
  have hundo : ∀ j r, originalAdmissible j r → originalAdmissible j (fun t => r (sigma t)) := by
    intro j r hr
    rw [hadm]
    show r (sigma (t0 j)) = e j
    rw [hfix]
    exact (hadm j r).mp hr
  obtain ⟨h0, hlt⟩ := APFB07a.realized_moves_off_a_costly_start originalAdmissible totalCost
    realized hA2 c hsum t0 e hadm i v hv (next (next (t0 i))) h3
  have hmove : realized i (next (next (t0 i))) ≠ realized i (t0 i) := by
    intro h
    rw [h, h0] at hlt
    exact lt_irrefl _ hlt
  exact APFB07b.rate_is_held_on_realized_history originalAdmissible totalCost realized hA2 hBW sigma
    next hsigma c hsum hundo i profile now D o hrec ho hfact (t0 i) hmove


universe apfNative_uX apfNative_uP apfNative_uR apfNative_u_1 apfNative_u_2
theorem solution :
∀ {Interface : Type apfNative_u_1} {T : Type apfNative_u_2} [inst : Fintype.{apfNative_u_2} T]
  [DecidableEq.{apfNative_u_2 + 1} T] {X : Type apfNative_uX} {Process : Type apfNative_uP} {R : Type apfNative_uR}
  (originalAdmissible : Interface → (T → R) → Prop) (totalCost : Interface → (T → R) → Real)
  (realized : Interface → T → R)
  (hA2 :
    @APFB07a.A2Selection.{apfNative_u_1, max apfNative_uR apfNative_u_2} Interface (fun (i : Interface) => T → R)
      originalAdmissible totalCost realized)
  (hBW :
    @APFB07b.BWUniqueMinimum.{apfNative_u_1, max apfNative_uR apfNative_u_2} Interface (fun (i : Interface) => T → R)
      originalAdmissible totalCost)
  (sigma : Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) (next : T → T)
  (hsigma :
    ∀ (t : T),
      @Eq.{apfNative_u_2 + 1} T
        (next
          (@DFunLike.coe.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
            (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T (fun (x : T) => T)
            (@EquivLike.toFunLike.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
              (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T T
              (@Equiv.instEquivLike.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T))
            sigma (next t)))
        (@DFunLike.coe.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
          (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T (fun (x : T) => T)
          (@EquivLike.toFunLike.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
            (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T T
            (@Equiv.instEquivLike.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T))
          sigma t))
  (c : Interface → R → Real)
  (hsum :
    ∀ (i : Interface) (r : T → R),
      @Eq.{1} Real (totalCost i r)
        (@Finset.sum.{apfNative_u_2, 0} T Real Real.instAddCommMonoid (@Finset.univ.{apfNative_u_2} T inst)
          fun (t : T) => c i (r t)))
  (t0 : Interface → T) (e : Interface → R)
  (hadm : ∀ (i : Interface) (r : T → R), Iff (originalAdmissible i r) (@Eq.{apfNative_uR + 1} R (r (t0 i)) (e i)))
  (hfix :
    ∀ (i : Interface),
      @Eq.{apfNative_u_2 + 1} T
        (@DFunLike.coe.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
          (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T (fun (x : T) => T)
          (@EquivLike.toFunLike.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
            (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T T
            (@Equiv.instEquivLike.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T))
          sigma (t0 i))
        (t0 i))
  (i : Interface) (v : R) (hv : @LT.lt.{0} Real Real.instLT (c i v) (c i (e i)))
  (h3 : @Ne.{apfNative_u_2 + 1} T (next (next (t0 i))) (t0 i)) (profile : X → Process → Prop) (now : X → R) (D : X → X)
  (o : T → X) (hrec : ∀ (t : T), @Eq.{apfNative_uR + 1} R (realized i t) (now (o t)))
  (ho : ∀ (t : T), @Eq.{apfNative_uX + 1} X (o (next t)) (D (o t)))
  (hfact :
    ∀ (r : R),
      @APFB01.Descends.{apfNative_uX, apfNative_uP} X Process profile fun (x : X) =>
        @Eq.{apfNative_uR + 1} R (now (D x)) r),
  And
    (@Eq.{apfNative_uR + 1} R
      (now
        (o
          (@DFunLike.coe.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
            (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T (fun (x : T) => T)
            (@EquivLike.toFunLike.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
              (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T T
              (@Equiv.instEquivLike.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T))
            sigma (next (t0 i)))))
      (now (o (next (t0 i)))))
    (@Ne.{apfNative_uX + 1} (@APFB01.PhysicalState.{apfNative_uX, apfNative_uP} X Process profile)
      (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile
        (o
          (@DFunLike.coe.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
            (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T (fun (x : T) => T)
            (@EquivLike.toFunLike.{apfNative_u_2 + 1, apfNative_u_2 + 1, apfNative_u_2 + 1}
              (Equiv.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T) T T
              (@Equiv.instEquivLike.{apfNative_u_2 + 1, apfNative_u_2 + 1} T T))
            sigma (next (t0 i)))))
      (@APFB01.physicalClass.{apfNative_uX, apfNative_uP} X Process profile (o (next (t0 i))))) := by
  exact @APFB07b.rate_is_held_after_a_costly_start
