-- Prove2me | Definitions.Def_GalvinMultigraph_Gadget
-- name    : GalvinMultigraph_Gadget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:34:03.927347+00:00
-- url     : https://prove2.me/theorems/7a6c8bcf-8995-4e09-99f8-03e4b8a046fa
-- title:
--   Gadget
-- statement:
--   Definitions and structural lemmas for Gadget, from Juan Pablo Traverso Gianini (jtraverso/galvin-dinitz; see pinned Apache-2.0 LICENSE and source headers)'s pinned Galvin list edge-coloring theorem for bipartite multigraphs and Borodin-Kostochka-Woodall development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]
abbrev Left (A E : Type*) (k : ℕ) := A ⊕ (E × Fin k)
abbrev Right (B E : Type*) (k : ℕ) := B ⊕ (E × Fin k)
abbrev Vertex (A B E : Type*) (k : ℕ) := Left A E k ⊕ Right B E k
def cross (a : E → A) (b : E → B) : Left A E k → Right B E k → Prop
  | .inl _, .inl _ => False
  | .inl x, .inr (e, j) => a e = x ∧ j = 0
  | .inr (e, i), .inl y => b e = y ∧ i = 0
  | .inr (e, i), .inr (f, j) => e = f ∧ (i ≠ 0 ∨ j ≠ 0)
def graph (a : E → A) (b : E → B) : SimpleGraph (Vertex A B E k) where
  Adj
    | .inl u, .inr v => cross a b u v
    | .inr v, .inl u => cross a b u v
    | _, _ => False
  symm := ⟨by rintro (u | u) (v | v) h <;> exact h⟩
  loopless := ⟨by rintro (v | v) h <;> exact h⟩
noncomputable instance (a : E → A) (b : E → B) :
    DecidableRel (graph (k := k) a b).Adj := Classical.decRel _
def coloring (a : E → A) (b : E → B) : (graph (k := k) a b).Coloring (Fin 2) :=
  Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1)) (by
    rintro (u | u) (v | v) h <;> simp_all [graph])
def aEdge (a : E → A) (b : E → B) (e : E) : (graph (k := k) a b).edgeSet :=
  ⟨s(Sum.inl (Sum.inl (a e)), Sum.inr (Sum.inr (e, 0))), by simp [graph, cross]⟩
def bEdge (a : E → A) (b : E → B) (e : E) : (graph (k := k) a b).edgeSet :=
  ⟨s(Sum.inl (Sum.inr (e, 0)), Sum.inr (Sum.inl (b e))), by simp [graph, cross]⟩
def innerEdge (a : E → A) (b : E → B) (e : E) (i j : Fin k)
    (h : i ≠ 0 ∨ j ≠ 0) : (graph (k := k) a b).edgeSet :=
  ⟨s(Sum.inl (Sum.inr (e, i)), Sum.inr (Sum.inr (e, j))), by simp [graph, cross, h]⟩
def rowEdge (a : E → A) (b : E → B) (e : E) (i j : Fin k) :
    (graph (k := k) a b).edgeSet :=
  if h : i = 0 ∧ j = 0 then bEdge a b e
  else innerEdge a b e i j (by tauto)
def tag : Vertex A B E k → Option E
  | .inl (.inr (e, _)) => some e
  | .inr (.inr (e, _)) => some e
  | _ => none
open Classical in
noncomputable def tagList (P : E → Finset Color) : Option E → Option E → Finset Color
  | none, none => ∅
  | some e, none => P e
  | none, some e => P e
  | some e, some f => if e = f then P e else ∅
theorem tagList_symm (P : E → Finset Color) (x y : Option E) :
    tagList P x y = tagList P y x := by
  classical
  cases x with
  | none => cases y <;> rfl
  | some e =>
    cases y with
    | none => rfl
    | some f =>
      by_cases h : e = f
      · subst f; rfl
      · simp [tagList, h, Ne.symm h]
noncomputable def lists (a : E → A) (b : E → B) (P : E → Finset Color)
    (e : (graph (k := k) a b).edgeSet) : Finset Color :=
  Sym2.lift ⟨fun u v => tagList P (tag u) (tag v), fun _ _ => tagList_symm P _ _⟩ e.1
def index : Vertex A B E k → Fin k
  | .inl (.inr (_, i)) => i
  | .inr (.inr (_, i)) => i
  | _ => 0
end GalvinMultigraph.Gadget


