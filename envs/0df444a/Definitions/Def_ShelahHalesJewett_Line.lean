-- Prove2me | Definitions.Def_ShelahHalesJewett_Line
-- name    : ShelahHalesJewett_Line
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T04:50:06.666806+00:00
-- url     : https://prove2.me/theorems/025a25ad-7529-4d89-84be-dfeb49656041
-- title:
--   Line
-- statement:
--   Definitions and structural lemmas for Line, from Gabriel Dahia (gdahia/ShelahHalesJewett; see pinned Apache-2.0 LICENSE and source headers)'s pinned Shelah primitive-recursive bound for Hales-Jewett numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Line.lean

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Pigeonhole
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Combinatorics
variable {η α ι ι' κ : Type*}
namespace Line
def reindex (l : Line α ι) (e : ι ≃ ι') : Line α ι' where
  idxFun := l.idxFun ∘ e.symm
  proper := let ⟨i, hi⟩ := l.proper; ⟨e i, by simp [hi]⟩
@[simp]
lemma reindex_apply (l : Line α ι) (e : ι ≃ ι') (x : α) : l.reindex e x = l x ∘ e.symm := rfl
end Line
namespace Subspace
def prodLine (V : Subspace η α ι) (l : Line α ι') : Subspace (Option η) α (ι ⊕ ι') where
  idxFun := Sum.elim (fun i ↦ (V.idxFun i).map id some) fun i ↦ (l.idxFun i).elim (.inr none) .inl
  proper
    | none => let ⟨i, hi⟩ := l.proper; ⟨.inr i, by simp [hi]⟩
    | some e => let ⟨i, hi⟩ := V.proper e; ⟨.inl i, by simp [hi]⟩
@[simp]
lemma prodLine_apply (V : Subspace η α ι) (l : Line α ι') (x : Option η → α) :
    V.prodLine l x = Sum.elim (V (x ∘ some)) (l (x none)) := by
  funext i
  cases i with
  | inl i => cases h : V.idxFun i <;> simp [prodLine, coe_apply, h]
  | inr i => cases h : l.idxFun i <;> simp [prodLine, coe_apply, h]
def compLine (V : Subspace η α ι) (l : Line α η) : Line α ι where
  idxFun i := (V.idxFun i).elim some l.idxFun
  proper := let ⟨e, he⟩ := l.proper; let ⟨i, hi⟩ := V.proper e; ⟨i, by simp [hi, he]⟩
end Subspace
end Combinatorics


