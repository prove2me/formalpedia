-- Prove2me | Definitions.Def_GJKKL_Trajectory_Frozen
-- name    : GJKKL_Trajectory_Frozen
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:36:56.855008+00:00
-- url     : https://prove2.me/theorems/3d1752ce-3f13-459e-9389-0c2a5471b6ef
-- title:
--   Frozen
-- statement:
--   Definitions and structural lemmas for Frozen, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Frozen.lean

module
public import Definitions.Def_GJKKL_Greedy_Drift
public import Definitions.Def_GJKKL_History_Freedman
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical in
/-- The process `F t (d_v)`, frozen from the step at which `v` is covered. -/
noncomputable def frozen (H : Finset (Finset V)) (F : ℕ → ℝ → ℝ) (v : V) :
    List (Finset V) → ℝ
  | [] => F 0 (dv H [] v)
  | a :: h => if v ∈ covered (a :: h) then frozen H F v h else F (h.length + 1) (dv H (a :: h) v)
end GJKKL


