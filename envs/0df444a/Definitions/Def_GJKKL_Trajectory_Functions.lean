-- Prove2me | Definitions.Def_GJKKL_Trajectory_Functions
-- name    : GJKKL_Trajectory_Functions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:29:11.360646+00:00
-- url     : https://prove2.me/theorems/64185a65-3b8c-46e5-8b76-d118ffb9db60
-- title:
--   Functions
-- statement:
--   Definitions and structural lemmas for Functions, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Functions.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL.Trajectory
open Finset
noncomputable def pfrac (a : ℝ) (t : ℕ) : ℝ := 1 - t / a
end GJKKL.Trajectory


