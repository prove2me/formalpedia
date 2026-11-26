-- Prove2me | Definitions.Def_AlonTarsiChoosability_Solution
-- name    : AlonTarsiChoosability_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:24:23.852019+00:00
-- url     : https://prove2.me/theorems/027a1612-197e-4645-9237-8335a48604de
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/Solution.lean

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_AlonTarsi
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace OrientationColouring
open AlonTarsi
variable {V : Type*} [Fintype V] [DecidableEq V]
end OrientationColouring


