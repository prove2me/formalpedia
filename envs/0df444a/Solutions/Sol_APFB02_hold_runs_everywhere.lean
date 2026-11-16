-- Prove2me | solution 1 for APFB02.hold_runs_everywhere
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-15T22:43:59.613991+00:00
-- url     : https://prove2.me/submissions/7401f085-10e4-44da-84a8-3833ea702e54

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB02_hold_runs_everywhere
title: Where finitely many distinctions tell a region's states apart, a hold after which every combination of sides is still held runs at every state, is one to one and onto, can be taken again where it lands, and is undone by repeating it
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 17:21 HST ("It sounds like we should be able to derive that!"). The second hold
 reading adopted 2026-11-14 11:33 HST (RULING_hold_readings_2026-11-14), typed for a hold that need not run
 everywhere in Def_APFB02_HoldWhereItRuns. "Told apart" (the author, 2026-11-14 03:12 HST), used here as the
 hypothesis that the distinctions tell the states apart. FOUNDATION_INPUTS B02, second sentence, enters
 only through the reading. Thm_APFPaper5_K3_undone_where_it_lands (pass 50, the three conditions).
consumes_inputs: none as a declared predicate. Hypotheses: finitely many distinctions (hD, the instance);
 the distinctions tell the states apart (hsep); the adopted reading (h2).
statement: (stillHeldAfterOn_univ_iff) where the hold runs at every state the reading is the form typed
 before. (hold_reaches_every_state) under hsep and h2, every state is where the hold takes some state it
 runs at. (hold_bijective) so the hold is one to one and onto. (hold_runs_everywhere) and it runs at every
 state. (hold_goes_on, hold_erases_nothing_where_it_runs) so it can be taken again where it lands, and
 erases nothing. (hold_undone) so every move of the hold is undone from where it lands.
reading: "can be taken again where it lands" (condition 2 of pass 50) is not a further sentence. It follows
 from the second hold reading said of the hold as it runs, with "told apart" and finitely many distinctions.
 So does "erases nothing", without the first hold reading. The three conditions of pass 50 all follow.
not_claimed: that this follows from the eight declared forms (the reading and "told apart" are not declared
 inputs; a world of the eight in which it fails is in Thm_APFPaper5_Worlds_pass_world_undone); that a
 region has finitely many distinctions; that the reading is meant of the hold as it runs.
-/
import Definitions.Def_APFB02_HoldWhereItRuns
import Theorems.Thm_APFPaper5_K3_undone_of_erases_nothing_and_goes_on
import Theorems.Thm_APFPaper5_K3_undone_of_each_kind
import Theorems.Thm_APFPaper5_K3_undoneWhereItLands_of_turnsLoseNothing
import Theorems.Thm_APFPaper5_K3_erasing_is_not_undone
import Theorems.Thm_APFPaper5_K3_one_way_is_not_undone
import Theorems.Thm_APFPaper5_K3_endless_is_not_undone
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
open APFPaper5.K3

namespace APFB02

theorem stillHeldAfterOn_univ_iff {X D : Type*} (reads : D → X → Bool) (h : X → X) :
    StillHeldAfterOn reads (fun _ => True) h ↔ StillHeldAfter reads h := by
  constructor
  · intro hh S v
    obtain ⟨x, hx⟩ := hh S v
    exact ⟨x.1, hx⟩
  · intro hh S v
    obtain ⟨x, hx⟩ := hh S v
    exact ⟨⟨x, trivial⟩, hx⟩

theorem hold_reaches_every_state {X D : Type*} [Fintype D] (reads : D → X → Bool)
    (runs : X → Prop) (h : X → X)
    (hsep : ∀ x y : X, (∀ d : D, reads d x = reads d y) → x = y)
    (h2 : StillHeldAfterOn reads runs h) (y : X) : ∃ x : X, runs x ∧ h x = y := by
  obtain ⟨x, hx⟩ := h2 Finset.univ (fun d => reads d y)
  exact ⟨x.1, x.2, hsep _ _ (fun d => hx d (Finset.mem_univ d))⟩

theorem states_finite {X D : Type*} [Fintype D] (reads : D → X → Bool)
    (hsep : ∀ x y : X, (∀ d : D, reads d x = reads d y) → x = y) : Finite X :=
  Finite.of_injective (fun (x : X) (d : D) => reads d x)
    (fun x y e => hsep x y (fun d => congrFun e d))

theorem hold_bijective {X D : Type*} [Fintype D] (reads : D → X → Bool) (runs : X → Prop)
    (h : X → X) (hsep : ∀ x y : X, (∀ d : D, reads d x = reads d y) → x = y)
    (h2 : StillHeldAfterOn reads runs h) : Function.Bijective h := by
  have hF : Finite X := states_finite reads hsep
  have hsurj : Function.Surjective h := fun y => by
    obtain ⟨x, _, hx⟩ := hold_reaches_every_state reads runs h hsep h2 y
    exact ⟨x, hx⟩
  exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩

theorem hold_runs_everywhere {X D : Type*} [Fintype D] (reads : D → X → Bool) (runs : X → Prop)
    (h : X → X) (hsep : ∀ x y : X, (∀ d : D, reads d x = reads d y) → x = y)
    (h2 : StillHeldAfterOn reads runs h) (x0 : X) : runs x0 := by
  obtain ⟨x, hx, e⟩ := hold_reaches_every_state reads runs h hsep h2 (h x0)
  have e' : x = x0 := (hold_bijective reads runs h hsep h2).1 e
  rw [← e']
  exact hx

theorem hold_goes_on {X D : Type*} [Fintype D] (reads : D → X → Bool) (runs : X → Prop)
    (h : X → X) (hsep : ∀ x y : X, (∀ d : D, reads d x = reads d y) → x = y)
    (h2 : StillHeldAfterOn reads runs h) : GoesOn (fun u v : X => runs u ∧ v = h u) :=
  fun _ v _ => ⟨h v, hold_runs_everywhere reads runs h hsep h2 v, rfl⟩

theorem hold_erases_nothing_where_it_runs {X D : Type*} [Fintype D] (reads : D → X → Bool)
    (runs : X → Prop) (h : X → X)
    (hsep : ∀ x y : X, (∀ d : D, reads d x = reads d y) → x = y)
    (h2 : StillHeldAfterOn reads runs h) : ErasesNothing (fun u v : X => runs u ∧ v = h u) :=
  fun _ _ _ h1 h3 => (hold_bijective reads runs h hsep h2).1 (h1.2.symm.trans h3.2)

theorem hold_undone {X D : Type*} [Fintype D] (reads : D → X → Bool) (runs : X → Prop)
    (h : X → X) (hsep : ∀ x y : X, (∀ d : D, reads d x = reads d y) → x = y)
    (h2 : StillHeldAfterOn reads runs h) :
    UndoneWhereItLands (fun u v : X => runs u ∧ v = h u) := by
  have hF : Finite X := states_finite reads hsep
  exact undone_of_erases_nothing_and_goes_on _ (fun _ _ _ h1 h3 => h1.2.trans h3.2.symm)
    (hold_erases_nothing_where_it_runs reads runs h hsep h2) (hold_goes_on reads runs h hsep h2)

end APFB02


universe apfNative_u_1 apfNative_u_2
theorem solution :
∀ {X : Type apfNative_u_1} {D : Type apfNative_u_2} [Fintype.{apfNative_u_2} D] (reads : D → X → Bool) (runs : X → Prop)
  (h : X → X) (hsep : ∀ (x y : X), (∀ (d : D), @Eq.{1} Bool (reads d x) (reads d y)) → @Eq.{apfNative_u_1 + 1} X x y)
  (h2 : @APFB02.StillHeldAfterOn.{apfNative_u_1, apfNative_u_2} X D reads runs h) (x0 : X), runs x0 := by
  exact @APFB02.hold_runs_everywhere
