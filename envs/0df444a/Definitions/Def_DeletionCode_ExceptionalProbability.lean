-- Prove2me | Definitions.Def_DeletionCode_ExceptionalProbability
-- name    : DeletionCode_ExceptionalProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:38:07.109743+00:00
-- url     : https://prove2.me/theorems/e930ad3e-6884-4134-8197-dd97cf942a59
-- title:
--   Exceptional Probability
-- statement:
--   Definitions and structural lemmas for Exceptional Probability, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean

import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_SpectrumPath
set_option autoImplicit true
namespace DeletionCode.ExceptionalProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform
open ConflictGraphWitness
open scoped BigOperators
variable {n : ℕ}
def CandidatePartner (t k : ℕ) (x y : Bits n) : Prop :=
  x ≠ y ∧ ∃ (d : ℕ) (trace : AlignmentTrace.Trace),
    trace.source = List.ofFn x ∧ trace.target = List.ofFn y ∧
    trace.deletions = d ∧ trace.insertions = d ∧
    (d < t ∨ (d = t ∧ ¬ FiniteConflictGraph.Separated (4 * windowLength k) trace))
noncomputable def candidatePartners (t k : ℕ) (x : Bits n) : Finset (Bits n) := by
  classical
  exact Finset.univ.filter (CandidatePartner t k x)
noncomputable def collisionEvent (k Q : ℕ) (x y : Bits n) :
    Set (Gram (windowLength k) → ℝ) :=
  {weights | wordLabel Q (realWeightedHash weights) x =
    wordLabel Q (realWeightedHash weights) y}
noncomputable def exceptionalEvent (t k Q : ℕ) (x : Bits n) :
    Set (Gram (windowLength k) → ℝ) :=
  {weights | FiniteConflictGraph.Exceptional t k
    (wordLabel Q (realWeightedHash weights)) x}
end DeletionCode.ExceptionalProbability


