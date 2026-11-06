-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
-- name    : QEC_Locality_SeparatorProfile_StoppedRecursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:10:38.524483+00:00
-- url     : https://prove2.me/theorems/c9d09ef2-34a4-4581-9b4e-812101e14381
-- title:
--   Stopped Recursion
-- statement:
--   Definitions and structural lemmas for Stopped Recursion, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedRecursion.lean

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
set_option autoImplicit false
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def ReverseSymmetricEdgeSet (edges : Finset (ι × ι)) : Prop :=
  ∀ x y, (x, y) ∈ edges ↔ (y, x) ∈ edges
inductive EdgeRestrictedStoppedRecursion (G : ConnectivityGraph ι) (r : Nat) :
    Finset (ι × ι) → Finset ι → Type u
  | leaf {edges : Finset (ι × ι)} {vertices : Finset ι}
      (hsubset : edges ⊆ directedEdgeFinset G)
      (hsymmetric : ReverseSymmetricEdgeSet edges)
      (hincident : edgeIncidentVertices edges ⊆ vertices)
      (hcard : vertices.card ≤ r) :
      EdgeRestrictedStoppedRecursion G r edges vertices
  | split {edges : Finset (ι × ι)} {vertices left separator right : Finset ι}
      (hsubset : edges ⊆ directedEdgeFinset G)
      (hsymmetric : ReverseSymmetricEdgeSet edges)
      (hincident : edgeIncidentVertices edges ⊆ vertices)
      (hpartition :
        TwoThirdsBalancedPartitionAfterDeleting (edgeRestrictedGraph G edges)
          vertices left separator right)
      (hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize (edgeRestrictedGraph G edges) vertices)
      (hleft : (left ∪ separator).card < vertices.card)
      (hright : (right ∪ separator).card < vertices.card)
      (leftTree : EdgeRestrictedStoppedRecursion G r
        (separatorLeftEdges edges left) (left ∪ separator))
      (rightTree : EdgeRestrictedStoppedRecursion G r
        (separatorRightEdges edges left) (right ∪ separator)) :
      EdgeRestrictedStoppedRecursion G r edges vertices
def EdgeRestrictedStoppedRecursion.edgeOwnerType
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Type
  | .leaf _ _ _ _ => Unit
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      Sum leftTree.edgeOwnerType rightTree.edgeOwnerType
noncomputable instance EdgeRestrictedStoppedRecursion.edgeOwnerFintype
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    Fintype tree.edgeOwnerType := by
  induction tree with
  | leaf _ _ _ _ =>
      change Fintype Unit
      infer_instance
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      change Fintype (Sum leftTree.edgeOwnerType rightTree.edgeOwnerType)
      letI := ihLeft
      letI := ihRight
      infer_instance
noncomputable instance EdgeRestrictedStoppedRecursion.edgeOwnerDecidableEq
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    DecidableEq tree.edgeOwnerType := by
  induction tree with
  | leaf _ _ _ _ =>
      change DecidableEq Unit
      infer_instance
  | split _ _ _ _ _ _ _ leftTree rightTree ihLeft ihRight =>
      change DecidableEq (Sum leftTree.edgeOwnerType rightTree.edgeOwnerType)
      letI := ihLeft
      letI := ihRight
      infer_instance
noncomputable def EdgeRestrictedStoppedRecursion.edgeRegion
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) →
      tree.edgeOwnerType → Finset (ι × ι)
  | .leaf (edges := edges) _ _ _ _, _ => edges
  | .split _ _ _ _ _ _ _ leftTree rightTree, owner =>
      match owner with
      | Sum.inl owner => leftTree.edgeRegion owner
      | Sum.inr owner => rightTree.edgeRegion owner
noncomputable def EdgeRestrictedStoppedRecursion.edgeActive
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) : Finset tree.edgeOwnerType := by
  classical
  exact Finset.univ.filter fun owner => (tree.edgeRegion owner).Nonempty
noncomputable def EdgeRestrictedStoppedRecursion.terminalOwnerCount
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Nat
  | .leaf _ _ _ _ => 1
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      leftTree.terminalOwnerCount + rightTree.terminalOwnerCount
noncomputable def EdgeRestrictedStoppedRecursion.edgeOwnerAncestors
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) →
      tree.edgeOwnerType → Finset ι
  | .leaf _ _ _ _, _ => ∅
  | .split (separator := separator) _ _ _ _ _ _ _ leftTree rightTree, owner =>
      match owner with
      | Sum.inl owner => separator ∪ leftTree.edgeOwnerAncestors owner
      | Sum.inr owner => separator ∪ rightTree.edgeOwnerAncestors owner
end QEC.Locality


