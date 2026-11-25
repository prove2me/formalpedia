-- Prove2me | Definitions.Def_MooreGraphsHoffmanSingleton_Solution
-- name    : MooreGraphsHoffmanSingleton_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:20:27.621742+00:00
-- url     : https://prove2.me/theorems/acdd6554-e11f-4770-ba30-04a618638364
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/moore-graphs-hoffman-singleton; see pinned Apache-2.0 LICENSE and source headers)'s pinned Moore graphs of diameter two: the Hoffman-Singleton theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/moore-graphs-hoffman-singleton/blob/8819ccfea5474fab3d1cbc17e703860a4e008254/Solution.lean

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphs
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace HoffmanSingleton
variable {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj]
end HoffmanSingleton


