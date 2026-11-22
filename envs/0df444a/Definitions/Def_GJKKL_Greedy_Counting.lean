-- Prove2me | Definitions.Def_GJKKL_Greedy_Counting
-- name    : GJKKL_Greedy_Counting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:34:50.683687+00:00
-- url     : https://prove2.me/theorems/2576f331-6ef0-47aa-9692-3272ed16d12c
-- title:
--   Counting
-- statement:
--   Definitions and structural lemmas for Counting, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_History_Freedman
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
def ManyAvail (H : Finset (Finset V)) (g : ℕ → ℝ) : List (Finset V) → Prop :=
  AliveBefore (fun h => g h.length ≤ ((avail H h).card : ℝ))
end GJKKL


