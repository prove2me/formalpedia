-- Prove2me | Definitions.Def_DeletionCode_ConflictGraphWitness
-- name    : DeletionCode_ConflictGraphWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:34:42.792185+00:00
-- url     : https://prove2.me/theorems/a8096eb3-b969-4eb6-ba17-1f17cb99fbad
-- title:
--   Conflict Graph Witness
-- statement:
--   Definitions and structural lemmas for Conflict Graph Witness, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConflictGraphWitness.lean

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_WordGraphWitness
import Definitions.Def_DeletionCode_CircleHash
set_option autoImplicit true
namespace DeletionCode.ConflictGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks AlignmentTrace WitnessCases
abbrev Spectrum (k : ℕ) := Gram (windowLength k) → ℤ
noncomputable def spectrum {n : ℕ} (k : ℕ) (x : Bits n) : Spectrum k :=
  wordSpectrum (padBits x) n (windowLength k)
noncomputable def wordLabel {n k : ℕ} (Q : ℕ) (H : Spectrum k →+ UnitAddCircle) (x : Bits n) : ℤ :=
  CircleHash.label Q (H (spectrum k x))
def catalogue (t k : ℕ) : Set (Spectrum k) := {w | CatalogueRule t k w}
def surviving {k : ℕ} (t Q : ℕ) (H : Spectrum k →+ UnitAddCircle) : Set (Spectrum k) :=
  CircleHash.surviving H Q (catalogue t k)
abbrev Vertex {n k : ℕ} (t Q : ℕ) (H : Spectrum k →+ UnitAddCircle) :=
  FiniteConflictGraph.Vertex (n := n) t k (wordLabel Q H)
noncomputable def graph {n k : ℕ} (t Q : ℕ) (H : Spectrum k →+ UnitAddCircle) :
    SimpleGraph (Vertex (n := n) t Q H) :=
  FiniteConflictGraph.graph t k (wordLabel Q H)
def SeparatedCoverage (t k n : ℕ) : Prop :=
  ∀ (x y : Bits n), KUnique (padBits x) n k → ∀ trace : Trace,
    trace.source = List.ofFn x → trace.target = List.ofFn y →
    trace.deletions = t → trace.insertions = t →
    FiniteConflictGraph.Separated (4 * windowLength k) trace →
    CatalogueRule t k (spectrum k y - spectrum k x)
end DeletionCode.ConflictGraphWitness


