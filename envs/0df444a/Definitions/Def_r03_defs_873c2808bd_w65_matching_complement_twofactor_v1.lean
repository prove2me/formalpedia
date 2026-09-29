-- Prove2me | Definitions.Def_r03_defs_873c2808bd_w65_matching_complement_twofactor_v1
-- name    : r03_defs_873c2808bd_w65_matching_complement_twofactor_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:21:16.054457+00:00
-- url     : https://prove2.me/theorems/d41e6b17-1812-44bd-b27b-272589ab7f6a
-- title:
--   R03 P3-factor definition module: r03_defs_873c2808bd_w65_matching_complement_twofactor_v1
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/w65_matching_complement_twofactor_v1.lean; source SHA-256 47e93163e71ec0eaa9138243aefcc39b4e51524f44854f442eca645a0427fe3b; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03MatchingComplementTwoFactor

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

def FAdj (G M : SimpleGraph V) (a b : V) : Prop :=
  G.Adj a b ∧ ¬ M.Adj a b

def FNeighbors (G M : SimpleGraph V) (v : V) :=
  {w : V // FAdj G M v w}

noncomputable def neighborPartitionEquiv
    (G M : SimpleGraph V) (v : V) (hMsub : M ≤ G) :
    ({w : V // M.Adj v w} ⊕ FNeighbors G M v) ≃
      {w : V // G.Adj v w} := by
  classical
  let toFun : ({w : V // M.Adj v w} ⊕ FNeighbors G M v) →
      {w : V // G.Adj v w} := fun x =>
    match x with
    | Sum.inl w => ⟨w.1, hMsub w.2⟩
    | Sum.inr w => ⟨w.1, w.2.1⟩
  let invFun : {w : V // G.Adj v w} →
      ({w : V // M.Adj v w} ⊕ FNeighbors G M v) := fun w =>
    if h : M.Adj v w.1 then
      Sum.inl ⟨w.1, h⟩
    else
      Sum.inr ⟨w.1, w.2, h⟩
  refine {
    toFun := toFun
    invFun := invFun
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    rcases x with w | w
    · simp [toFun, invFun, w.property]
    · have hn : ¬ M.Adj v w.1 := w.2.2
      simp only [invFun, dif_neg hn, toFun]
      apply congrArg Sum.inr
      exact Subtype.ext (by rfl)
  · intro w
    by_cases h : M.Adj v w.1
    · simp [toFun, invFun, h]
    · simp [toFun, invFun, h]

end R03MatchingComplementTwoFactor


