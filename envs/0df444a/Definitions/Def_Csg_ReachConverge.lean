-- Prove2me | Definitions.Def_Csg_ReachConverge
-- name    : Csg_ReachConverge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:49:47.074641+00:00
-- url     : https://prove2.me/theorems/d516d8e1-c0c3-4100-aab8-9f4ec18aef9d
-- title:
--   Reach Converge
-- statement:
--   Definitions and structural lemmas for Reach Converge, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachConverge.lean

import Definitions.Def_Csg_ReachOp
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
set_option autoImplicit true
namespace Csg
noncomputable instance : Fact ((0 : ℝ) ≤ 1) := ⟨by norm_num⟩
namespace CSG
open OmegaCompletePartialOrder Filter Topology
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
end CSG
end Csg


