-- Prove2me | solution 1 for APFPaper5.K3.undone_of_erases_nothing_and_goes_on
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:37:48.552489+00:00
-- url     : https://prove2.me/submissions/6f8d01fb-d88e-42b1-90db-987b8bda1f98

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFPaper5_K3_undone_where_it_lands
title: A move that erases nothing, can be taken again from where it lands, and leads to finitely many places is undone by repeating it; each of the three conditions is needed
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's ruling of 2026-11-14 16:52 HST and question "Does this fall from the 8? What conditions
 are needed" (RULING_loses_nothing_across_contexts_2026-11-14). Thm_APFPaper5_K3_held_states_and_undo (this
 seat, 2026-11-13: undoing is repeating, on one set of states). The other Claude seat's
 TEE_UP_named_waiting_on_author_2026-11-14 ("what is needed is that the repeat is admitted"; not typed
 there). FOUNDATION_INPUTS is not consumed.
consumes_inputs: none. Plain mathematics about a relation on a set of places.
statement: (undone_of_erases_nothing_and_goes_on) on finitely many places, a move with one outcome that
 erases nothing and can be taken again from where it lands is undone, from where it lands, by repeating it.
 (undone_of_each_kind) the same for several kinds of move, each meeting the three conditions.
 (undoneWhereItLands_of_turnsLoseNothing) the first typed form of "loses nothing" gives the reading across
 contexts, on one set of states. (erasing_is_not_undone, one_way_is_not_undone, endless_is_not_undone)
 three small relations, each meeting two of the three conditions and failing the third, in which a move is
 not undone.
reading: the conditions are: nothing is erased; the move can be taken again where it lands; the places it
 can lead to are finitely many. Then undoing is repeating.
not_claimed: that any of the three follows from the declared inputs; that a physical move meets them. The
 three small relations are not worlds of the eight declared forms; the world that meets the eight and fails
 the reading is in Thm_APFPaper5_Worlds_pass_world_undone.
-/
import Definitions.Def_APFPaper5_K3_UndoneWhereItLands
import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return

set_option autoImplicit false
namespace APFPaper5.K3

universe u

theorem undone_of_erases_nothing_and_goes_on {N : Type u} [Finite N] (mv : N → N → Prop)
    (hone : OneOutcome mv) (hinj : ErasesNothing mv) (hon : GoesOn mv) : UndoneWhereItLands mv := by
  intro u v huv
  obtain ⟨f, hf⟩ : ∃ f : {a : N // ∃ b, mv a b} → {a : N // ∃ b, mv a b}, ∀ s, mv s.1 (f s).1 :=
    ⟨fun s => ⟨Classical.choose s.2, hon _ _ (Classical.choose_spec s.2)⟩,
      fun s => Classical.choose_spec s.2⟩
  have finj : Function.Injective f := fun s t h =>
    Subtype.ext (hinj s.1 t.1 (f s).1 (hf s) (by rw [h]; exact hf t))
  have hstep : ∀ (k : ℕ) (s : {a : N // ∃ b, mv a b}),
      Relation.ReflTransGen mv s.1 (f^[k] s).1 := by
    intro k
    induction k with
    | zero => intro s; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro s
      rw [Function.iterate_succ_apply']
      exact Relation.ReflTransGen.tail (ih s) (hf _)
  obtain ⟨k, n, hn, hk⟩ := every_state_comes_to_return f ⟨u, v, huv⟩
  have hret : f^[n] ⟨u, v, huv⟩ = ⟨u, v, huv⟩ := by
    have h1 : f^[k] (f^[n] ⟨u, v, huv⟩) = f^[k] ⟨u, v, huv⟩ := by
      rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply]
      exact hk
    exact (finj.iterate k) h1
  have hfu : (f ⟨u, v, huv⟩).1 = v := hone u _ v (hf ⟨u, v, huv⟩) huv
  have hback : f^[n - 1] (f ⟨u, v, huv⟩) = ⟨u, v, huv⟩ := undo_is_a_repeat f _ n hn hret
  have h2 := hstep (n - 1) (f ⟨u, v, huv⟩)
  rw [hback, hfu] at h2
  exact h2

theorem undone_of_each_kind {N : Type u} [Finite N] {I : Type*} (mv : I → N → N → Prop)
    (h : ∀ i : I, OneOutcome (mv i) ∧ ErasesNothing (mv i) ∧ GoesOn (mv i)) :
    UndoneWhereItLands (fun u v : N => ∃ i : I, mv i u v) := by
  rintro u v ⟨i, hi⟩
  have key : ∀ a b : N, Relation.ReflTransGen (mv i) a b →
      Relation.ReflTransGen (fun u v : N => ∃ i : I, mv i u v) a b := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨i, hbc⟩
  exact key v u (undone_of_erases_nothing_and_goes_on (mv i) (h i).1 (h i).2.1 (h i).2.2 u v hi)

theorem undoneWhereItLands_of_turnsLoseNothing {S : Type u} (Adm : Set (S → S))
    (h : TurnsLoseNothing Adm) : UndoneWhereItLands (fun u v : S => ∃ f ∈ Adm, f u = v) := by
  rintro u v ⟨f, hf, hfu⟩
  obtain ⟨g, hg, hgf⟩ := h f hf
  exact Relation.ReflTransGen.single ⟨g, hg, by rw [← hfu]; exact hgf u⟩

/-- Everything goes to one place. One outcome, goes on, two places; it erases, and is not undone. -/
theorem erasing_is_not_undone :
    OneOutcome (fun _ v : Bool => v = true) ∧ GoesOn (fun _ v : Bool => v = true) ∧
      ¬ UndoneWhereItLands (fun _ v : Bool => v = true) := by
  refine ⟨fun _ _ _ h1 h2 => h1.trans h2.symm, fun _ _ _ => ⟨true, rfl⟩, fun h => ?_⟩
  have key : ∀ a b : Bool, Relation.ReflTransGen (fun _ v : Bool => v = true) a b →
      a = true → b = true := by
    intro a b hab
    induction hab with
    | refl => exact fun ha => ha
    | tail _ hbc _ => exact fun _ => hbc
  exact Bool.noConfusion (key true false (h false true rfl) rfl)

/-- One place leads to another and nothing leads on. One outcome, erases nothing, two places; it does not
go on, and is not undone. -/
theorem one_way_is_not_undone :
    OneOutcome (fun u v : Bool => u = false ∧ v = true) ∧
      ErasesNothing (fun u v : Bool => u = false ∧ v = true) ∧
      ¬ UndoneWhereItLands (fun u v : Bool => u = false ∧ v = true) := by
  refine ⟨fun _ _ _ h1 h2 => h1.2.trans h2.2.symm, fun _ _ _ h1 h2 => h1.1.trans h2.1.symm,
    fun h => ?_⟩
  have key : ∀ a b : Bool, Relation.ReflTransGen (fun u v : Bool => u = false ∧ v = true) a b →
      a = true → b = true := by
    intro a b hab
    induction hab with
    | refl => exact fun ha => ha
    | tail _ hbc _ => exact fun _ => hbc.2
  exact Bool.noConfusion (key true false (h false true ⟨rfl, rfl⟩) rfl)

/-- Each place leads to the next, without end. One outcome, erases nothing, goes on; the places are not
finitely many, and no move is undone. -/
theorem endless_is_not_undone :
    OneOutcome (fun u v : ℕ => v = u + 1) ∧ ErasesNothing (fun u v : ℕ => v = u + 1) ∧
      GoesOn (fun u v : ℕ => v = u + 1) ∧ ¬ UndoneWhereItLands (fun u v : ℕ => v = u + 1) := by
  refine ⟨fun _ _ _ h1 h2 => h1.trans h2.symm,
    fun u u' v h1 h2 => Nat.succ.inj (h1.symm.trans h2), fun _ v _ => ⟨v + 1, rfl⟩, fun h => ?_⟩
  have key : ∀ a b : ℕ, Relation.ReflTransGen (fun u v : ℕ => v = u + 1) a b → a ≤ b := by
    intro a b hab
    induction hab with
    | refl => exact le_refl a
    | tail _ hbc ih => exact le_trans ih (by rw [hbc]; exact Nat.le_succ _)
  exact absurd (key 1 0 (h 0 1 rfl)) (by decide)

end APFPaper5.K3


universe apfNative_u
theorem solution :
∀ {N : Type apfNative_u} [Finite.{apfNative_u + 1} N] (mv : N → N → Prop)
  (hone : @APFPaper5.K3.OneOutcome.{apfNative_u} N mv) (hinj : @APFPaper5.K3.ErasesNothing.{apfNative_u} N mv)
  (hon : @APFPaper5.K3.GoesOn.{apfNative_u} N mv), @APFPaper5.K3.UndoneWhereItLands.{apfNative_u} N mv := by
  exact @APFPaper5.K3.undone_of_erases_nothing_and_goes_on
