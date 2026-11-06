-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
-- name    : QEC_Locality_SeparatorProfile_StoppedPotential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:48:28.225315+00:00
-- url     : https://prove2.me/theorems/e586b82b-c76c-4de7-95e1-2cb2bfd82ab7
-- title:
--   Stopped Potential
-- statement:
--   Definitions and structural lemmas for Stopped Potential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/StoppedPotential.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Theorems.Thm_QEC_Locality_AssumedBGKLMeasuredProfilePowerUpperBound_edgeRestricted
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_profileSeparator_child_card_lt
import Theorems.Thm_QEC_Locality_separatorLeftEdges_incident_subset
import Theorems.Thm_QEC_Locality_separatorLeftEdges_reverse
import Theorems.Thm_QEC_Locality_separatorLeftEdges_subset_directed
import Theorems.Thm_QEC_Locality_separatorRightEdges_incident_subset
import Theorems.Thm_QEC_Locality_separatorRightEdges_reverse
import Theorems.Thm_QEC_Locality_separatorRightEdges_subset_directed

set_option autoImplicit false
noncomputable section
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
def EdgeRestrictedStoppedRecursion.StoppedAtScale
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Prop
  | .leaf _ _ _ _ => True
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      r < vertices.card ∧ leftTree.StoppedAtScale ∧ rightTree.StoppedAtScale
noncomputable def buildQuantitativeStoppedRecursion
    (G : ConnectivityGraph ι) (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : exponent < 1) (r : Nat)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (edges : Finset (ι × ι)) (vertices : Finset ι)
    (hsubset : edges ⊆ directedEdgeFinset G)
    (hsymmetric : ReverseSymmetricEdgeSet edges)
    (hincident : edgeIncidentVertices edges ⊆ vertices) :
    { tree : EdgeRestrictedStoppedRecursion G r edges vertices // tree.StoppedAtScale } := by
  classical
  by_cases hterminal : vertices.card ≤ r
  · exact ⟨.leaf hsubset hsymmetric hincident hterminal, trivial⟩
  · let H := edgeRestrictedGraph G edges
    let left := measuredTwoThirdsLeft H vertices
    let separator := measuredTwoThirdsSeparator H vertices
    let right := measuredTwoThirdsRight H vertices
    have hlarge : r < vertices.card := Nat.lt_of_not_ge hterminal
    have hseparatorThreshold : profileSeparatorThreshold beta exponent ≤ r :=
      (Nat.le_max_left _ _).trans hthreshold
    have hscale : profileSeparatorThreshold beta exponent ≤ vertices.card :=
      hseparatorThreshold.trans hlarge.le
    have hvertices : 1 ≤ vertices.card := by omega
    have hpartition : TwoThirdsBalancedPartitionAfterDeleting H vertices left separator right :=
      measuredTwoThirdsSplit_spec H vertices
    have hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize H vertices :=
      (measuredTwoThirdsSeparator_spec H vertices).2.2
    have hprofileH := hProfile.edgeRestricted G beta exponent edges
    have hleftRaw : left.card + separator.card < vertices.card :=
      profileSeparator_child_card_lt H beta exponent hprofileH hexponent
        hvertices hscale hminimum hpartition.2.2.2.1
    have hrightRaw : right.card + separator.card < vertices.card :=
      profileSeparator_child_card_lt H beta exponent hprofileH hexponent
        hvertices hscale hminimum hpartition.2.2.2.2.1
    have hleft : (left ∪ separator).card < vertices.card :=
      (Finset.card_union_le left separator).trans_lt hleftRaw
    have hright : (right ∪ separator).card < vertices.card :=
      (Finset.card_union_le right separator).trans_lt hrightRaw
    let leftResult := buildQuantitativeStoppedRecursion G beta exponent hProfile hexponent r
      hthreshold (separatorLeftEdges edges left) (left ∪ separator)
      (separatorLeftEdges_subset_directed G edges left hsubset)
      (separatorLeftEdges_reverse edges left hsymmetric)
      (separatorLeftEdges_incident_subset G edges vertices left separator right
        hsubset hsymmetric hincident hpartition)
    let rightResult := buildQuantitativeStoppedRecursion G beta exponent hProfile hexponent r
      hthreshold (separatorRightEdges edges left) (right ∪ separator)
      (separatorRightEdges_subset_directed G edges left hsubset)
      (separatorRightEdges_reverse edges left hsymmetric)
      (separatorRightEdges_incident_subset G edges vertices left separator right
        hsubset hsymmetric hincident hpartition)
    exact ⟨.split hsubset hsymmetric hincident hpartition hminimum hleft hright
      leftResult.1 rightResult.1, hlarge, leftResult.2, rightResult.2⟩
termination_by vertices.card
decreasing_by
  · exact hleft
  · exact hright
noncomputable def EdgeRestrictedStoppedRecursion.separatorCharge
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Nat
  | .leaf _ _ _ _ => 0
  | .split (separator := separator) _ _ _ _ _ _ _ leftTree rightTree =>
      separator.card + leftTree.separatorCharge + rightTree.separatorCharge
noncomputable def EdgeRestrictedStoppedRecursion.terminalPotentialMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (beta exponent : ℝ) :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) → ℝ
  | .leaf _ _ _ _ => profileDivisionPotential beta exponent r vertices.card
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      leftTree.terminalPotentialMass beta exponent +
        rightTree.terminalPotentialMass beta exponent
noncomputable def EdgeRestrictedStoppedRecursion.terminalCarrierMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Nat
  | .leaf _ _ _ _ => vertices.card
  | .split _ _ _ _ _ _ _ leftTree rightTree =>
      leftTree.terminalCarrierMass + rightTree.terminalCarrierMass
noncomputable def leftRefinedBoundary
    (boundary left separator : Finset ι) : Finset ι :=
  separator ∪ (boundary ∩ (left ∪ separator))
noncomputable def rightRefinedBoundary
    (boundary right separator : Finset ι) : Finset ι :=
  separator ∪ (boundary ∩ (right ∪ separator))
noncomputable def EdgeRestrictedStoppedRecursion.propagatedBoundary
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) →
      Finset ι → tree.edgeOwnerType → Finset ι
  | .leaf (edges := edges) _ _ _ _, boundary, _ =>
      boundary ∩ edgeIncidentVertices edges
  | .split (left := left) (separator := separator) (right := right)
      _ _ _ _ _ _ _ leftTree rightTree, boundary, owner =>
      match owner with
      | Sum.inl owner =>
          leftTree.propagatedBoundary (leftRefinedBoundary boundary left separator) owner
      | Sum.inr owner =>
          rightTree.propagatedBoundary (rightRefinedBoundary boundary right separator) owner
noncomputable def EdgeRestrictedStoppedRecursion.propagatedBoundaryMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι} :
    EdgeRestrictedStoppedRecursion G r edges vertices → Finset ι → Nat
  | .leaf (edges := edges) _ _ _ _, boundary =>
      (boundary ∩ edgeIncidentVertices edges).card
  | .split (left := left) (separator := separator) (right := right)
      _ _ _ _ _ _ _ leftTree rightTree, boundary =>
      leftTree.propagatedBoundaryMass (leftRefinedBoundary boundary left separator) +
        rightTree.propagatedBoundaryMass (rightRefinedBoundary boundary right separator)
def profileDivisionChargeRootConstant (beta exponent : ℝ) : ℝ :=
  profileDivisionPotentialCoefficient beta exponent /
    (3 * (1 / 4 : ℝ) ^ (1 - exponent))
def profileDivisionBoundaryRatioConstant (beta exponent : ℝ) : ℝ :=
  profileDivisionPotentialCoefficient beta exponent /
    ((1 / 4 : ℝ) ^ (1 - exponent) *
      (beta / (1 - markedSpineDecayRatio exponent)))
def profileDivisionRegionConstant (beta exponent : ℝ) : ℝ :=
  4 + 4 * profileDivisionChargeRootConstant beta exponent +
    2 * profileDivisionBoundaryRatioConstant beta exponent
end QEC.Locality


