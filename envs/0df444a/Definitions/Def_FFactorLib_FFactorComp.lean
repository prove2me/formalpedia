-- Prove2me | Definitions.Def_FFactorLib_FFactorComp
-- name    : FFactorLib_FFactorComp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:50:35.884972+00:00
-- url     : https://prove2.me/theorems/60472c62-fd3f-4e5c-a40f-fa7685d35b3e
-- title:
--   FFactor Comp
-- statement:
--   Definitions and structural lemmas for FFactor Comp, from Juan Pablo Traverso Gianini (jtraverso/tutte-f-factor; see pinned Apache-2.0 LICENSE and source headers)'s pinned Tutte f-factor theorem for finite simple graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorComp.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace FFactor
section Label
variable {X L : Type*} (H : SimpleGraph X) (φ : X → L)
end Label
section Removal
variable {W : Type*} (Γ : SimpleGraph W)
abbrev del (U : Set W) : SimpleGraph ((⊤ : Γ.Subgraph).deleteVerts U).verts :=
  ((⊤ : Γ.Subgraph).deleteVerts U).coe
@[simp] theorem del_adj {U : Set W} {a b : ((⊤ : Γ.Subgraph).deleteVerts U).verts} :
    (del Γ U).Adj a b ↔ Γ.Adj a b := by
  constructor
  · intro h; exact Subgraph.coe_adj_sub _ _ _ h
  · intro h; exact Subgraph.deleteVerts_adj.mpr ⟨trivial, a.2.2, trivial, b.2.2, h⟩
def delIncl (U : Set W) (x : W) : del Γ U →g del Γ (U \ {x}) where
  toFun a := ⟨a.1, ⟨trivial, fun h => a.2.2 h.1⟩⟩
  map_rel' h := (del_adj Γ (U := U \ {x})).mpr ((del_adj Γ (U := U)).mp h)
def TwoComp (U : Set W) (x : W) : Prop :=
  ∀ a b c : ((⊤ : Γ.Subgraph).deleteVerts U).verts, Γ.Adj x a → Γ.Adj x b →
      Γ.Adj x c → (del Γ U).Reachable a b ∨ (del Γ U).Reachable a c ∨
        (del Γ U).Reachable b c
end Removal
end FFactor


