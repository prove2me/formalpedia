-- Prove2me | Definitions.Def_FFactorLib_FFactorSuff
-- name    : FFactorLib_FFactorSuff
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:54:56.830793+00:00
-- url     : https://prove2.me/theorems/8a0708f8-f107-4aa7-92db-e623f4a0ee52
-- title:
--   FFactor Suff
-- statement:
--   Definitions and structural lemmas for FFactor Suff, from Juan Pablo Traverso Gianini (jtraverso/tutte-f-factor; see pinned Apache-2.0 LICENSE and source headers)'s pinned Tutte f-factor theorem for finite simple graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.gadget_adj_inl_inl
attribute [local simp] FFactor.gadget_adj_inl_inr
attribute [local simp] FFactor.gadget_adj_inr_inl
attribute [local simp] FFactor.gadget_adj_inr_inr
attribute [local simp] FFactor.mem_del_verts


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph Classical
namespace FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
section Normal
variable {U : Set (GV G f)}
theorem inner_mem_of_inner_mem (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V}
    {i j : Fin (G.degree v - f v)} (hi : (.inr ⟨v, i⟩ : GV G f) ∈ U) :
    (.inr ⟨v, j⟩ : GV G f) ∈ U := by
  by_contra hj
  apply hmin _ hi
  intro a b c ha hb hc
  let y0 : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts :=
    ⟨.inr ⟨v, j⟩, (mem_del_verts _).mpr hj⟩
  have key : ∀ a : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts,
      (gadget G f).Adj (.inr ⟨v, i⟩) a → (del (gadget G f) U).Reachable a y0 := by
    rintro ⟨a | q, haU⟩ ha
    · exact Adj.reachable ((del_adj _).mpr (show (gadget G f).Adj (.inl a) (.inr ⟨v, j⟩) from ha))
    · exact absurd ha (gadget_adj_inr_inr _ _)
  exact Or.inl ((key a ha).trans (key b hb).symm)
variable (G f U) in
/-- `T`: vertices all of whose inner vertices lie in `U`. -/
noncomputable def Tset : Finset V :=
  {v | ∀ i : Fin (G.degree v - f v), (.inr ⟨v, i⟩ : GV G f) ∈ U}
variable (G f U) in
/-- `S`: vertices not in `T` all of whose outer vertices lie in `U`. -/
noncomputable def Sset : Finset V :=
  {v | v ∉ Tset G f U ∧ ∀ d : G.Dart, d.fst = v → (.inl d : GV G f) ∈ U}
theorem mem_Tset {v : V} : v ∈ Tset G f U ↔ ∀ i, (.inr ⟨v, i⟩ : GV G f) ∈ U := by
  simp [Tset]
theorem F1 (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V} (hv : v ∉ Tset G f U)
    (i : Fin (G.degree v - f v)) : (.inr ⟨v, i⟩ : GV G f) ∉ U := by
  intro hi
  exact hv (mem_Tset.mpr (fun j => inner_mem_of_inner_mem hmin hi))
end Normal
section Label
variable [DecidableEq V] {U : Set (GV G f)}
variable (G f U) in
/-- The vertex of `G` a vertex of the gadget "belongs to" after removing `U`. -/
noncomputable def home : GV G f → V
  | .inl d => if d.fst ∈ Tset G f U then d.snd else d.fst
  | .inr p => p.1
variable (G f U) in
/-- The graph `G - (S ∪ T)`. -/
abbrev Gr : SimpleGraph ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) :=
  G.induce (((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ)
variable (G f U) in
/-- The labelling of the vertices of the gadget whose fibres are the components of
`gadget - U`. -/
noncomputable def lab (a : GV G f) : (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f) :=
  if h : home G f U a ∉ Sset G f U ∪ Tset G f U then
    .inl ((Gr G f U).connectedComponentMk ⟨home G f U a, h⟩)
  else match a with
    | .inl d => .inr (.inl d.edge)
    | .inr _ => .inr (.inr a)
theorem notMem_T_of_notMem_union {r : V} (hr : r ∉ Sset G f U ∪ Tset G f U) :
    r ∉ Tset G f U := fun h => hr (mem_union_right _ h)
end Label
end FFactor


