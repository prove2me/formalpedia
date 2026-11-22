-- Prove2me | Definitions.Def_GJKKL_Main_Theorem
-- name    : GJKKL_Main_Theorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:42:09.057273+00:00
-- url     : https://prove2.me/theorems/c187fc25-19c9-4a99-b2e0-16514c302e6a
-- title:
--   Theorem
-- statement:
--   Definitions and structural lemmas for Theorem, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Theorem.lean

module
public import Definitions.Def_GJKKL_Main_TrackParams
public import Definitions.Def_GJKKL_Numerics_Final
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory GJKKL.History GJKKL.Numerics
noncomputable def gfun (V : Type*) [Fintype V] (k : ℕ) (ε d a : ℝ) (m i : ℕ) : ℝ :=
  if i < m then aPar V k i * (dhat k d a i - delta k ε d a i) else 0
end GJKKL.Main


