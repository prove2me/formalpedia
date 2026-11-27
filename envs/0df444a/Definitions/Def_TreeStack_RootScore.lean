-- Prove2me | Definitions.Def_TreeStack_RootScore
-- name    : TreeStack_RootScore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:30:05.612597+00:00
-- url     : https://prove2.me/theorems/4ea57ac6-4ede-4733-88c0-bb75d761a13d
-- title:
--   Root Score
-- statement:
--   Definitions and structural lemmas for Root Score, from jfairfaxball-348 (jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees; see pinned Apache-2.0 LICENSE and README.md)'s pinned TreeStack: Csernák-Soukup stacking number equality stack(T) = estim(T) for nontrivial trees development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/RootScore.lean

import Mathlib
import Definitions.Def_TreeStack_Boundary
set_option autoImplicit false
namespace TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
def incidentBranch (T : FiniteTree V) (r u : V)
    (h : T.graph.Adj u r) : OrientedBranch T where
  root := u
  parent := r
  adj := h
noncomputable def rootMessageTerm
    (T : FiniteTree V) (C : Configuration V) (r u : V) : ℤ :=
  if h : T.graph.Adj u r then
    OrientedBranch.messageContribution
      (OrientedBranch.branchMessage C (incidentBranch T r u h))
  else
    0
noncomputable def rootMessageSum
    (T : FiniteTree V) (C : Configuration V) (r : V) : ℤ :=
  ∑ u : V, rootMessageTerm T C r u
noncomputable def score
    (T : FiniteTree V) (C : Configuration V) (r : V) : ℤ :=
  (C r : ℤ) + rootMessageSum T C r
def IsOccupiedRootNeighbor
    (T : FiniteTree V) (C : Configuration V) (r u : V) : Prop :=
  ∃ h : T.graph.Adj u r, (incidentBranch T r u h).Occupied C
def RootTask
    (T : FiniteTree V) (C : Configuration V) (r : V) :=
  {u : V // IsOccupiedRootNeighbor T C r u}
noncomputable instance RootTask.instFintype
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    Fintype (RootTask T C r) :=
  Fintype.ofInjective
    (fun t : RootTask T C r => (t.1 : V))
    Subtype.val_injective
noncomputable def RootTask.branch
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) : OrientedBranch T :=
  incidentBranch T r t.1 (Classical.choose t.2)
noncomputable def RootTask.gain
    {T : FiniteTree V} {C : Configuration V} {r : V}
    (t : RootTask T C r) : ℤ :=
  OrientedBranch.messageContribution
    (OrientedBranch.branchMessage C t.branch)
noncomputable def rootTasks
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    List (RootTask T C r) := by
  classical
  exact (Finset.univ : Finset (RootTask T C r)).toList
noncomputable def rootSignatureFluxSum
    (m : MoveSignature T) (r : V) : ℤ :=
  ∑ u : V,
    ((m.count u r : ℤ) - 2 * (m.count r u : ℤ))
end TreeStack


