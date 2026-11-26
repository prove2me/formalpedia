-- Prove2me | Definitions.Def_HajnalSzemeredi_Final
-- name    : HajnalSzemeredi_Final
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T23:05:48.017306+00:00
-- url     : https://prove2.me/theorems/32bf3154-605a-4a60-bcd8-f3e15256f973
-- title:
--   Final
-- statement:
--   Definitions and structural lemmas for Final, from Juan Pablo Traverso Gianini (jtraverso/hajnal-szemeredi; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hajnal-Szemeredi theorem on equitable vertex colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Final.lean

module
public import Definitions.Def_HajnalSzemeredi_Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sum
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Classical Finset
namespace HajnalSzemeredi
variable {V : Type*} [Fintype V]
def padAdj (G : SimpleGraph V) (p : ℕ) : V ⊕ Fin p → V ⊕ Fin p → Prop
  | .inl u, .inl v => G.Adj u v
  | .inr i, .inr j => i ≠ j
  | _, _ => False
def pad (G : SimpleGraph V) (p : ℕ) : SimpleGraph (V ⊕ Fin p) where
  Adj := padAdj G p
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp only [padAdj] at h ⊢
    · exact h.symm
    · exact Ne.symm h⟩
  loopless := ⟨fun a h => by
    cases a <;> simp only [padAdj] at h
    · exact G.loopless.irrefl _ h
    · exact h rfl⟩
end HajnalSzemeredi


