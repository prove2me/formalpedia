-- Prove2me | Definitions.Def_MooreLib_MooreGraphsAux
-- name    : MooreLib_MooreGraphsAux
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:11:42.805075+00:00
-- url     : https://prove2.me/theorems/4f8ca502-05f9-52bc-a431-b6eb1ec7eb1e
-- title:
--   Moore Graphs Aux
-- statement:
--   Definitions and structural lemmas for Moore Graphs Aux, from Juan Pablo Traverso Gianini (jtraverso/moore-graphs-hoffman-singleton; see pinned Apache-2.0 LICENSE and source headers)'s pinned Moore graphs of diameter two: the Hoffman-Singleton theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphsAux.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph Matrix
namespace MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def ball2 [DecidableEq V] (v : V) : Finset V :=
  insert v (G.neighborFinset v ∪ (G.neighborFinset v).biUnion fun u => (G.neighborFinset u).erase v)
end MooreGraphs


