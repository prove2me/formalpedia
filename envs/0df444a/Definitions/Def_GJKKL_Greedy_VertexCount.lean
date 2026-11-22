-- Prove2me | Definitions.Def_GJKKL_Greedy_VertexCount
-- name    : GJKKL_Greedy_VertexCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:31:34.530947+00:00
-- url     : https://prove2.me/theorems/e4611c2c-76f1-4f7f-a144-6c778c2119df
-- title:
--   Vertex Count
-- statement:
--   Definitions and structural lemmas for Vertex Count, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/VertexCount.lean

module
public import Definitions.Def_GJKKL_Statement
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
end GJKKL


