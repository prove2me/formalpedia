-- Prove2me | Definitions.Def_GJKKL_Greedy_Drift
-- name    : GJKKL_Greedy_Drift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:35:51.761078+00:00
-- url     : https://prove2.me/theorems/57956df4-3ab8-4cc4-888f-3015c0fde1b7
-- title:
--   Drift
-- statement:
--   Definitions and structural lemmas for Drift, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Drift.lean

module
public import Definitions.Def_GJKKL_Greedy_Degrees
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
def lossSum (H : Finset (Finset V)) (h : List (Finset V)) (v : V) : ℕ :=
  ∑ a ∈ avail H h \ Dv H h v, ((Dv H h v).filter (fun f => ¬ Disjoint f a)).card
def hitters (H : Finset (Finset V)) (h : List (Finset V)) (v : V) (f : Finset V) :
    Finset (Finset V) :=
  (avail H h \ Dv H h v).filter (fun a => ¬ Disjoint f a)
end GJKKL


