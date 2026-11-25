-- Prove2me | Definitions.Def_MooreLib_MooreGraphs
-- name    : MooreLib_MooreGraphs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:15:45.935207+00:00
-- url     : https://prove2.me/theorems/f9c1227f-48c0-4d2d-b5e5-1236cfe2bd9d
-- title:
--   Moore Graphs
-- statement:
--   Definitions and structural lemmas for Moore Graphs, from Juan Pablo Traverso Gianini (jtraverso/moore-graphs-hoffman-singleton; see pinned Apache-2.0 LICENSE and source headers)'s pinned Moore graphs of diameter two: the Hoffman-Singleton theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/MooreLib/MooreGraphs.lean

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace MooreGraphs
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
end MooreGraphs


