-- Prove2me | Definitions.Def_DeletionCode_ObstructionProbability
-- name    : DeletionCode_ObstructionProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:59:31.29537+00:00
-- url     : https://prove2.me/theorems/75ec2b81-5f92-42e0-9dc6-074673e32b4c
-- title:
--   Obstruction Probability
-- statement:
--   Definitions and structural lemmas for Obstruction Probability, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean

import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Definitions.Def_DeletionCode_WitnessCounting
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
namespace DeletionCode.ObstructionProbability
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open CircleHash CircleUniform ConflictGraphWitness WitnessCounting
open scoped BigOperators ENNReal
variable {n : ℕ}
def cutoff (t k : ℕ) : ℕ := 1 + 4 * t * (windowLength k) ^ 2
noncomputable def ruleTestEvent (k Q : ℕ) (U : RuleSet k) :
    Set (Gram (windowLength k) → ℝ) :=
  {weights | ∀ u ∈ U, ‖realWeightedHash weights u‖ < 1 / (Q : ℝ)}
noncomputable def candidateEvent (t k Q R : ℕ) (x : Bits n) :
    Set (Gram (windowLength k) → ℝ) :=
  {weights | ∃ U : RuleSet k, Candidate t (padBits x) n k R U ∧
    weights ∈ ruleTestEvent k Q U}
noncomputable def obstructionEvent (t k Q : ℕ) (x : Bits n) :
    Set (Gram (windowLength k) → ℝ) :=
  {weights | ∃ v : Vertex (n := n) t Q (realWeightedHash weights),
    v.val = x ∧
      ¬ ((graph t Q (realWeightedHash weights)).connectedComponentMk v).toSimpleGraph.Colorable 2}
end DeletionCode.ObstructionProbability


