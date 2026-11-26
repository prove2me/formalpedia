-- Prove2me | Definitions.Def_Sabidussi_OddBalance
-- name    : Sabidussi_OddBalance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:07:06.184815+00:00
-- url     : https://prove2.me/theorems/59c59e79-7cf1-5add-8dd1-dfc73aa86677
-- title:
--   Odd Balance
-- statement:
--   Definitions and structural lemmas for Odd Balance, from Upstream contributors (gexahedron/sabidussi-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Sabidussi compatibility conjecture for finite Eulerian loop multigraphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OddBalance.lean

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
set_option autoImplicit true
open scoped BigOperators
open Finset
namespace Sabidussi
namespace OddBalance
abbrev F2 := ZMod 2
section
variable {V : Type*} [Fintype V] [DecidableEq V]
def obstruction (b : V → V → Fin 3 → Fin 3 → F2) (x : V → Fin 3) (v : V) : F2 :=
  ∑ u ∈ Finset.univ.erase v, b v u (x v) (x u)
def solutions (b : V → V → Fin 3 → Fin 3 → F2) : Finset (V → Fin 3) :=
  Finset.univ.filter fun x => ∀ v, obstruction b x v = 0
abbrev Choice (S : Finset V) :=
  (v : {v // v ∈ S}) → {u : V // u ≠ v}
def choiceTerm (b : V → V → Fin 3 → Fin 3 → F2) (S : Finset V)
    (f : Choice S) (x : V → Fin 3) : F2 :=
  ∏ v : {v // v ∈ S}, b v (f v) (x v) (x (f v))
def totalChoiceTerm (b : V → V → Fin 3 → Fin 3 → F2)
    (S : Finset V) (f : Choice S) : F2 :=
  ∑ x : V → Fin 3, choiceTerm b S f x
def Derangement (S : Finset V) :=
  {σ : Equiv.Perm {v // v ∈ S} // ∀ v, σ v ≠ v}
noncomputable instance Derangement.instFintype (S : Finset V) : Fintype (Derangement S) :=
  Fintype.ofInjective
    (fun d : Derangement S => (d.1 : {v // v ∈ S} → {v // v ∈ S})) <| by
      intro d e h
      apply Subtype.ext
      apply Equiv.ext
      exact congrFun h
def Derangement.choice {S : Finset V} (d : Derangement S) : Choice S :=
  fun v => ⟨d.1 v, by
    intro h
    exact d.2 v (Subtype.ext h)⟩
def Derangement.inv {S : Finset V} (d : Derangement S) : Derangement S :=
  ⟨d.1.symm, fun v h => d.2 v <| by
    calc
      d.1 v = d.1 (d.1.symm v) := congrArg d.1 h.symm
      _ = v := d.1.apply_symm_apply v⟩
def CoveredChoice (S : Finset V) :=
  {f : Choice S // ∀ w : {w // w ∈ S}, ∃ v, (f v : V) = w}
noncomputable instance CoveredChoice.instFintype (S : Finset V) :
    Fintype (CoveredChoice S) :=
  Fintype.ofInjective (fun f : CoveredChoice S => f.1) Subtype.val_injective
noncomputable def CoveredChoice.toDerangement {S : Finset V}
    (c : CoveredChoice S) : Derangement S := by
  let r : {w // w ∈ S} → {v // v ∈ S} := fun w => Classical.choose (c.2 w)
  have hr (w : {w // w ∈ S}) : (c.1 (r w) : V) = w :=
    Classical.choose_spec (c.2 w)
  have rinj : Function.Injective r := by
    intro w z h
    apply Subtype.ext
    calc
      (w : V) = c.1 (r w) := (hr w).symm
      _ = c.1 (r z) := by rw [h]
      _ = z := hr z
  have rsurj : Function.Surjective r :=
    (Finite.injective_iff_surjective.mp rinj)
  have hmem (v : {v // v ∈ S}) : (c.1 v : V) ∈ S := by
    obtain ⟨w, rfl⟩ := rsurj v
    rw [hr]
    exact w.2
  let g : {v // v ∈ S} → {v // v ∈ S} := fun v => ⟨c.1 v, hmem v⟩
  have gsurj : Function.Surjective g := by
    intro w
    obtain ⟨v, hv⟩ := c.2 w
    exact ⟨v, Subtype.ext hv⟩
  let σ : Equiv.Perm {v // v ∈ S} :=
    Equiv.ofBijective g ((Fintype.bijective_iff_surjective_and_card g).2 ⟨gsurj, rfl⟩)
  exact ⟨σ, fun v hv => (c.1 v).2 <| by
    have := congrArg Subtype.val hv
    exact this⟩
def Derangement.toCoveredChoice {S : Finset V} (d : Derangement S) : CoveredChoice S :=
  ⟨d.choice, fun w => ⟨d.1.symm w, by
    exact congrArg Subtype.val (d.1.apply_symm_apply w)⟩⟩
lemma CoveredChoice.toDerangement_choice {S : Finset V} (c : CoveredChoice S) :
    c.toDerangement.choice = c.1 := by
  funext v
  apply Subtype.ext
  rfl
lemma Derangement.choice_injective {S : Finset V} :
    Function.Injective (fun d : Derangement S => d.choice) := by
  intro d e h
  apply Subtype.ext
  apply Equiv.ext
  intro v
  apply Subtype.ext
  simpa [Derangement.choice] using congrArg Subtype.val (congrFun h v)
noncomputable def coveredChoiceEquivDerangement (S : Finset V) :
    CoveredChoice S ≃ Derangement S where
  toFun := CoveredChoice.toDerangement
  invFun := Derangement.toCoveredChoice
  left_inv c := by
    apply Subtype.ext
    exact CoveredChoice.toDerangement_choice c
  right_inv d := by
    apply Derangement.choice_injective
    exact CoveredChoice.toDerangement_choice d.toCoveredChoice
end
end OddBalance
end Sabidussi


