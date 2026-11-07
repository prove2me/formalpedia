-- Prove2me | Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
-- name    : QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:08:29.358248+00:00
-- url     : https://prove2.me/theorems/45e85fe6-57b5-4e93-8049-4d2284163a14
-- title:
--   Witness Trees
-- statement:
--   Definitions and structural lemmas for Witness Trees, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
namespace QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
def closedNeighbors (i : I) : Finset I := insert i (G.neighborFinset i)
def WitnessTree : ℕ → I → Type u
  | 0, _ => PEmpty
  | h + 1, i => ∀ j : closedNeighbors G i, Option (WitnessTree h j)
instance witnessTreeFintype (h : ℕ) (i : I) : Fintype (WitnessTree G h i) := by
  induction h generalizing i with
  | zero => exact inferInstanceAs (Fintype PEmpty)
  | succ h ih =>
    letI (j : I) : Fintype (WitnessTree G h j) := ih j
    exact inferInstanceAs (Fintype (∀ j : closedNeighbors G i, Option (WitnessTree G h j)))
noncomputable def witnessWeight (p : I → ℝ) : (h : ℕ) → (i : I) → WitnessTree G h i → ℝ
  | 0, _, t => PEmpty.elim t
  | h + 1, i, t => p i * ∏ j : closedNeighbors G i,
      (t j).elim 1 (witnessWeight p h j)
noncomputable def witnessPartition (p : I → ℝ) (h : ℕ) (i : I) : ℝ :=
  ∑ t : WitnessTree G h i, witnessWeight G p h i t
noncomputable def resamplingBudget (x : I → ℝ) (i : I) : ℝ := x i / (1 - x i)
end QEC.Coding.ProbabilisticConstruction.Resampling


