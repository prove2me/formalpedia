-- Prove2me | Definitions.Def_FFactorLib_FFactorGadget
-- name    : FFactorLib_FFactorGadget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:50:41.442937+00:00
-- url     : https://prove2.me/theorems/e11b2e60-17f5-4ae7-b7fc-8399bc605608
-- title:
--   FFactor Gadget
-- statement:
--   Definitions and structural lemmas for FFactor Gadget, from Juan Pablo Traverso Gianini (jtraverso/tutte-f-factor; see pinned Apache-2.0 LICENSE and source headers)'s pinned Tutte f-factor theorem for finite simple graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph Classical
namespace FFactor
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)
abbrev GV := G.Dart ⊕ (Σ v : V, Fin (G.degree v - f v))
def gadgetAdj : GV G f → GV G f → Prop
  | .inl d, .inl d' => d' = d.symm
  | .inl d, .inr p => d.fst = p.1
  | .inr p, .inl d => d.fst = p.1
  | .inr _, .inr _ => False
noncomputable def gadget : SimpleGraph (GV G f) where
  Adj := gadgetAdj G f
  symm := ⟨by
    intro x y h
    rcases x with d | p <;> rcases y with d' | p' <;> simp only [gadgetAdj] at h ⊢
    · rw [h, Dart.symm_symm]
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro x h
    rcases x with d | p <;> simp only [gadgetAdj] at h
    exact Dart.symm_ne _ h.symm⟩
variable {G f}
end FFactor


