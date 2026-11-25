-- Prove2me | Definitions.Def_LeanPool_Vizing_Main
-- name    : LeanPool_Vizing_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T01:01:13.735777+00:00
-- url     : https://prove2.me/theorems/8cf7dc65-013a-4274-9a3c-62d47b7b8a50
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/LeanPool/Vizing/Main.lean

module
public import Definitions.Def_LeanPool_Vizing_Step
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right


set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace LeanPool.Vizing
namespace PEC
variable {V : Type*} [Fintype V] [DecidableEq V] {C : Type*} [Fintype C] [DecidableEq C]
  {G : SimpleGraph V}
def empty (G : SimpleGraph V) (C : Type*) : PEC G C where
  col := fun _ _ => none
  col_symm := fun _ _ => rfl
  col_adj := by intro u v γ h; exact absurd h (by simp)
  col_proper := by intro u v w γ h; exact absurd h (by simp)
noncomputable def uncoloured [DecidableRel G.Adj] (c : PEC G C) : Finset (V × V) :=
  {p ∈ (Finset.univ : Finset (V × V)) | G.Adj p.1 p.2 ∧ c.col p.1 p.2 = none}
def edgeOption (c : PEC G C) (e : Sym2 V) : Option C :=
  Sym2.lift ⟨c.col, c.col_symm⟩ e
omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
@[simp] lemma edgeOption_mk (c : PEC G C) (u v : V) :
    c.edgeOption s(u, v) = c.col u v := rfl
omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
/-- Totality supplies a colour on every actual edge, even for an empty palette. -/
lemma edgeOption_ne_none (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) :
    c.edgeOption e.1 ≠ none := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [SimpleGraph.mem_edgeSet] at he
    exact htot u v he
noncomputable def edgeColor (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) : C :=
  Classical.choose (Option.ne_none_iff_exists'.mp (c.edgeOption_ne_none htot e))
omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma edgeOption_eq_some_edgeColor (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) (e : G.edgeSet) :
    c.edgeOption e.1 = some (c.edgeColor htot e) :=
  Classical.choose_spec (Option.ne_none_iff_exists'.mp (c.edgeOption_ne_none htot e))
noncomputable def lineGraphColoring (c : PEC G C)
    (htot : ∀ u v, G.Adj u v → c.col u v ≠ none) : (G.lineGraph).Coloring C :=
  Coloring.mk (c.edgeColor htot) (by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ hadj
    rw [lineGraph_adj_iff_exists] at hadj
    obtain ⟨hne, v, hv₁, hv₂⟩ := hadj
    obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.1 hv₁
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv₂
    intro hcol
    have hγ := c.edgeOption_eq_some_edgeColor htot ⟨s(v, u), he₁⟩
    have hδ := c.edgeOption_eq_some_edgeColor htot ⟨s(v, w), he₂⟩
    simp only [edgeOption_mk] at hγ hδ
    rw [← hcol] at hδ
    have huw : u = w := c.col_proper hγ hδ
    subst huw
    exact hne (Subtype.ext rfl))
end PEC
end LeanPool.Vizing
namespace SimpleGraph
end SimpleGraph


