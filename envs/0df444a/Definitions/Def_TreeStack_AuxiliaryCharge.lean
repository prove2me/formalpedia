-- Prove2me | Definitions.Def_TreeStack_AuxiliaryCharge
-- name    : TreeStack_AuxiliaryCharge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:07:06.604252+00:00
-- url     : https://prove2.me/theorems/a1497937-1f22-4e2a-a336-df4f2e516464
-- title:
--   Auxiliary Charge
-- statement:
--   Definitions and structural lemmas for Auxiliary Charge, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/AuxiliaryCharge.lean

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
namespace OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
noncomputable def auxEdgeContribution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  -(auxWeightInt C ambientRoot hScores B.parent *
        messageContribution (branchMessage C B) +
      auxWeightInt C ambientRoot hScores B.root *
        messageContribution (branchMessage C B.reverseBranch))
noncomputable def retainedDefectCharge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  if B.DefectiveSupportEdge C then
    auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
      scoreDefect T C (B.rootedOwner ambientRoot)
  else
    0
noncomputable def emptyBoundaryCharge
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T) : ℤ :=
  if B.SupportEdge C then
    0
  else
    auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
      scoreDefect T C (B.rootedOwner ambientRoot)
end OrientedBranch
end TreeStack


