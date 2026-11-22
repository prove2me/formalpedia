-- Prove2me | Definitions.Def_GJKKL_Trajectory_Increments
-- name    : GJKKL_Trajectory_Increments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:37:36.094385+00:00
-- url     : https://prove2.me/theorems/0fa37b38-82a8-4795-ae2b-a8d9274fe41a
-- title:
--   Increments
-- statement:
--   Definitions and structural lemmas for Increments, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Increments.lean

module
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Definitions.Def_GJKKL_Trajectory_Trend
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
def Tracked (H : Finset (Finset V)) (dh δ : ℕ → ℝ) (h : List (Finset V)) : Prop :=
  ∀ u, u ∉ covered h → |(dv H h u : ℝ) - dh h.length| ≤ δ h.length
end GJKKL


