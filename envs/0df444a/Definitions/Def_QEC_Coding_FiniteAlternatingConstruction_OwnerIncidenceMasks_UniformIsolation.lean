-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:12:02.457498+00:00
-- url     : https://prove2.me/theorems/441b4106-1e5e-4ae8-a8b8-f1b64d9025e1
-- title:
--   Uniform Isolation
-- statement:
--   Definitions and structural lemmas for Uniform Isolation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformIsolation.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
set_option autoImplicit false
namespace QEC.Coding.BDL26UniformTopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
noncomputable abbrev graph (S : OddScale) (n : Nat) := decodingGraph S (n + 1)
abbrev Node (S : OddScale) (n : Nat) := (graph S n).Node
def topNode (S : OddScale) (n : Nat) (v : Vertex (state S n).presentation) : Node S n :=
  ⟨(Fin.last (n + 1)), v⟩
def TopMarksAreZ (S : OddScale) (n : Nat) (M : Finset (Node S n)) : Prop :=
  ∀ v : Vertex (state S n).presentation,
    topNode S n v ∈ M → ∃ z, v = Vertex.z z
def markedAdjacent (S : OddScale) (n : Nat) (M : Finset (Node S n)) (u v : {w : Node S n // w ∈ M}) : Prop :=
  (graph S n).adjacent u.val v.val
noncomputable def markedComponent (S : OddScale) (n : Nat) (M : Finset (Node S n)) (a : {w : Node S n // w ∈ M}) :
    Finset {w : Node S n // w ∈ M} :=
  Finset.univ.filter (Relation.ReflTransGen (markedAdjacent S n M) a)
end QEC.Coding.BDL26UniformTopOwnerIsolation


