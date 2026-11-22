-- Prove2me | Definitions.Def_GJKKL_Greedy_Degrees
-- name    : GJKKL_Greedy_Degrees
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:35:17.620634+00:00
-- url     : https://prove2.me/theorems/57bf5b69-c902-4a09-996e-cece569ca783
-- title:
--   Degrees
-- statement:
--   Definitions and structural lemmas for Degrees, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Degrees.lean

module
public import Definitions.Def_GJKKL_Greedy_Process
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
def Dv (H : Finset (Finset V)) (h : List (Finset V)) (v : V) : Finset (Finset V) :=
  (avail H h).filter (fun e => v ∈ e)
def dv (H : Finset (Finset V)) (h : List (Finset V)) (v : V) : ℕ := (Dv H h v).card
def uncovered (h : List (Finset V)) : Finset V := univ \ covered h
end GJKKL


