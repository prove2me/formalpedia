-- Prove2me | Definitions.Def_Mycielski_Basic
-- name    : Mycielski_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:23:21.851294+00:00
-- url     : https://prove2.me/theorems/54ecc763-6e67-40c4-8bce-5f5756c191a4
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Juan Pablo Traverso Gianini (jtraverso/erdos-girth-chromatic; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphs of large girth and large chromatic number: Erdos, Mycielski and Tutte development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Basic.lean

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Fintype.Option
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Mycielski
open SimpleGraph
universe u
abbrev Vertex (V : Type u) := Option (V × Bool)
def original {V : Type u} (v : V) : Vertex V := some (v, false)
def shadow {V : Type u} (v : V) : Vertex V := some (v, true)
def Adj {V : Type u} (G : SimpleGraph V) : Vertex V → Vertex V → Prop
  | some (v, false), some (w, false) => G.Adj v w
  | some (v, false), some (w, true) => G.Adj v w
  | some (v, true), some (w, false) => G.Adj v w
  | none, some (_, true) => True
  | some (_, true), none => True
  | _, _ => False
def graph {V : Type u} (G : SimpleGraph V) : SimpleGraph (Vertex V) where
  Adj := Adj G
  symm := ⟨by
    rintro (_ | ⟨v, bv⟩) (_ | ⟨w, bw⟩) <;>
      (try cases bv) <;> (try cases bw) <;>
      simp only [Adj] <;> first | exact id | exact G.adj_symm⟩
  loopless := ⟨by
    rintro (_ | ⟨v, b⟩)
    · simp [Adj]
    · cases b <;> simp [Adj]⟩
instance {V : Type u} (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (graph G).Adj := by
  rintro (_ | ⟨v, bv⟩) (_ | ⟨w, bw⟩) <;>
    (try cases bv) <;> (try cases bw) <;>
    dsimp only [graph, Adj] <;> infer_instance
def originalHom {V : Type u} (G : SimpleGraph V) : G →g graph G where
  toFun := original
  map_rel' := id
def originalEmbedding {V : Type u} (G : SimpleGraph V) : G ↪g graph G where
  toFun := original
  inj' := by
    intro v w h
    exact congrArg Prod.fst (Option.some.inj h)
  map_rel_iff' := Iff.rfl
end Mycielski


