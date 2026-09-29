-- Prove2me | Definitions.Def_r03_defs_e1150db1c7_w64_fixed_perfect_matching_bridge_v1
-- name    : r03_defs_e1150db1c7_w64_fixed_perfect_matching_bridge_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:21:00.572335+00:00
-- url     : https://prove2.me/theorems/61113cf0-9eb4-492c-801c-9649d8b0ced0
-- title:
--   R03 P3-factor definition module: r03_defs_e1150db1c7_w64_fixed_perfect_matching_bridge_v1
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/w64_fixed_perfect_matching_bridge_v1.lean; source SHA-256 c5c9bf1708cf052dcccc66b8a02668334f8b6fb7610fea6c6a123f30e7a35616; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03FixedPerfectMatchingBridge

open CubicP3Partition

universe u

variable {V : Type u} [Fintype V]

def FAdj (G M : SimpleGraph V) (a b : V) : Prop :=
  G.Adj a b ∧ ¬ M.Adj a b

def IsMatchingRelation (M : SimpleGraph V) : Prop :=
  ∀ ⦃v a b : V⦄, M.Adj v a → M.Adj v b → a = b

def P3PathProp (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c

def IntervalTile (G M : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    ((FAdj G M a b ∧ FAdj G M b c) ∨
      (M.Adj a b ∧ FAdj G M b c) ∨
      (FAdj G M a b ∧ M.Adj b c))

structure IntervalTileFactor (G M : SimpleGraph V) where
  blockCount : Nat
  place : (Fin blockCount × Fin 3) ≃ V
  tile : ∀ i : Fin blockCount,
    IntervalTile G M (place (i, 0)) (place (i, 1)) (place (i, 2))

end R03FixedPerfectMatchingBridge


