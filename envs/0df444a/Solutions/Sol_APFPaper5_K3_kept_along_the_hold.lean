-- Prove2me | solution 1 for APFPaper5.K3.kept_along_the_hold
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:08:58.867203+00:00
-- url     : https://prove2.me/submissions/12f56266-0bf6-4dc4-a710-1503a2cfa7dc

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_held_states_and_undo
title: On a state a hold brings back, the hold is undone by repeating it; with finitely many states every state comes to one the hold brings back; an occupant whose family each step keeps settles into such states
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's statement of 2026-11-13 ("can be undone is based on capacity. Is what's missing a detail
 about the occupant?"). FOUNDATION_INPUTS B01 (the quotient), B04 and B06 as worded ("its entire nonempty
 carried family"; the carried family is a finite set in the declared form). Thm_APFB01_undone_hold_returns.
consumes_inputs: B01's quotient in the theorem named APFB01. No input predicate is assumed.
statement: D is one step of a hold on a set of states.
 (undo_is_a_repeat) if n steps bring a state back, n - 1 more steps undo one step from it.
 (return_is_kept) the step of a state that is brought back is brought back.
 (undone_on_what_returns) on the states the hold brings back, one step loses nothing.
 (kept_along_the_hold) if each step keeps a property, every number of steps keeps it.
 (every_state_comes_to_return) with finitely many states, every state comes after some steps to a state
 the hold brings back.
 (occupant_settles) so if each step keeps a property that holds of a state, that state comes to states
 that still have the property, that the hold brings back, and from which a step is undone by repeating.
 (finite_of_separating_family) if a finite family of two-valued distinctions tells the states apart, the
 states are finitely many.
 (APFB01.every_object_comes_to_return) with finitely many processes, every physical object comes to one the
 hold brings back.
reading: "a hold can be undone" needs no input on the states the hold brings back. Finiteness, which is
 where capacity enters, brings every state to such states. What is left is that each step keeps the
 occupant's family and can be taken again.
not_claimed: that a hold acts on the states at an interface; that a step keeps the occupant's family or can
 be repeated; that capacity bounds the family (the chain bound of the repository is not used here); anything
 about a continuum of held states.
-/
import Theorems.Thm_APFB01_physicalState_finite
import Theorems.Thm_APFPaper5_K3_undone_hold_returns
import Theorems.Thm_APFB01_undone_hold_returns_every_object

set_option autoImplicit false

universe uX uP

namespace APFPaper5.K3

theorem undo_is_a_repeat {S : Type*} (D : S → S) (x : S) (n : ℕ) (hn : 0 < n)
    (h : D^[n] x = x) : D^[n - 1] (D x) = x := by
  have e : D^[n - 1 + 1] x = D^[n - 1] (D x) := rfl
  rw [← e, Nat.sub_add_cancel hn]
  exact h

theorem return_is_kept {S : Type*} (D : S → S) (x : S) (n : ℕ) (h : D^[n] x = x) :
    D^[n] (D x) = D x := by
  have e : D^[n] (D x) = D (D^[n] x) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  rw [e, h]

theorem undone_on_what_returns {S : Type*} (D : S → S) (x y : S) (n m : ℕ) (hn : 0 < n)
    (hm : 0 < m) (hx : D^[n] x = x) (hy : D^[m] y = y) (h : D x = D y) : x = y := by
  have px : D^[n * m] x = x := by
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hx m
  have py : D^[n * m] y = y := by
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed hy n
  have hpos : 0 < n * m := Nat.mul_pos hn hm
  calc x = D^[n * m - 1] (D x) := (undo_is_a_repeat D x (n * m) hpos px).symm
    _ = D^[n * m - 1] (D y) := by rw [h]
    _ = y := undo_is_a_repeat D y (n * m) hpos py

theorem kept_along_the_hold {S : Type*} (D : S → S) (P : S → Prop)
    (hP : ∀ s : S, P s → P (D s)) (o : S) (ho : P o) (n : ℕ) : P (D^[n] o) := by
  induction n with
  | zero => exact ho
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hP _ ih

theorem every_state_comes_to_return {S : Type*} [Finite S] (D : S → S) (x : S) :
    ∃ k n : ℕ, 0 < n ∧ D^[n] (D^[k] x) = D^[k] x := by
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => D^[n] x)
  have key : ∀ a b : ℕ, a < b → D^[a] x = D^[b] x →
      ∃ k n : ℕ, 0 < n ∧ D^[n] (D^[k] x) = D^[k] x := by
    intro a b hab h
    refine ⟨a, b - a, Nat.sub_pos_of_lt hab, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
    exact h.symm
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h e
  · exact key j i h e.symm

theorem occupant_settles {S : Type*} [Finite S] (D : S → S) (P : S → Prop)
    (hP : ∀ s : S, P s → P (D s)) (o : S) (ho : P o) :
    ∃ k n : ℕ, 0 < n ∧ P (D^[k] o) ∧ D^[n] (D^[k] o) = D^[k] o ∧
      D^[n - 1] (D (D^[k] o)) = D^[k] o := by
  obtain ⟨k, n, hn, h⟩ := every_state_comes_to_return D o
  exact ⟨k, n, hn, kept_along_the_hold D P hP o ho k, h, undo_is_a_repeat D _ n hn h⟩

theorem finite_of_separating_family {S : Type*} (F : Finset (S → Bool))
    (hsep : ∀ a b : S, (∀ d ∈ F, d a = d b) → a = b) : Finite S :=
  Finite.of_injective (fun (a : S) (d : F) => d.val a)
    (fun a b h => hsep a b (fun d hd => congrFun h ⟨d, hd⟩))

end APFPaper5.K3

theorem APFB01.every_object_comes_to_return {X : Type uX} {Process : Type uP} [Finite Process]
    (profile : X → Process → Prop)
    (D : APFB01.PhysicalState profile → APFB01.PhysicalState profile)
    (s : APFB01.PhysicalState profile) :
    ∃ k n : ℕ, 0 < n ∧ D^[n] (D^[k] s) = D^[k] s :=
  haveI := APFB01.physicalState_finite profile
  APFPaper5.K3.every_state_comes_to_return D s


universe apfNative_u_1
theorem solution :
∀ {S : Type apfNative_u_1} (D : S → S) (P : S → Prop) (hP : ∀ (s : S), P s → P (D s)) (o : S) (ho : P o) (n : Nat),
  P (@Nat.iterate.{apfNative_u_1 + 1} S D n o) := by
  exact @APFPaper5.K3.kept_along_the_hold
