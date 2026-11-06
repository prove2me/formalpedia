-- Prove2me | Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
-- name    : QEC_Locality_CorrectablePartition_SmallBoundary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:02:55.239256+00:00
-- url     : https://prove2.me/theorems/81a39476-2dc9-4036-a307-86580478b5a9
-- title:
--   Small Boundary
-- statement:
--   Definitions and structural lemmas for Small Boundary, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/SmallBoundary.lean

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_SeparatorProfile_Core
import Theorems.Thm_QEC_Locality_exists_minimumTwoThirdsBalancedVertexSeparator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def finiteSubsystemOfFinset (vertices : Finset ι) : FiniteSubsystem ι :=
  ⟨vertices⟩
structure BGKLSeparatorSplit
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices : Finset ι) where
  separator : Finset ι
  left : Finset ι
  right : Finset ι
  separator_subset : separator ⊆ vertices
  partition : left ∪ right = vertices \ separator
  disjoint : Disjoint left right
  left_balance : 3 * left.card ≤ 2 * vertices.card
  right_balance : 3 * right.card ≤ 2 * vertices.card
  noEdge : P.fixedGeneratorNoEdgeBetween left right
  separator_card : separator.card =
    P.fixedGeneratorMinimumTwoThirdsBalancedVertexSeparatorSize vertices
noncomputable def minimumBGKLSeparatorSplit
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices : Finset ι) : BGKLSeparatorSplit P vertices := by
  classical
  let witness :=
    exists_minimumTwoThirdsBalancedVertexSeparator
      P.fixedGeneratorInteractionGraph vertices
  let separator := Classical.choose witness
  have hseparator := Classical.choose_spec witness
  let leftWitness := hseparator.2.1
  let left := Classical.choose leftWitness
  let rightWitness := Classical.choose_spec leftWitness
  let right := Classical.choose rightWitness
  have hpartitionData := Classical.choose_spec rightWitness
  exact
    { separator := separator
      left := left
      right := right
      separator_subset := hseparator.1
      partition := hpartitionData.2.1
      disjoint := hpartitionData.2.2.1
      left_balance := hpartitionData.2.2.2.1
      right_balance := hpartitionData.2.2.2.2.1
      noEdge := hpartitionData.2.2.2.2.2
      separator_card := hseparator.2.2 }
theorem BGKLSeparatorSplit.left_card_lt
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    (hvertices : 0 < vertices.card) : split.left.card < vertices.card := by
  have hbalance := split.left_balance
  omega
theorem BGKLSeparatorSplit.right_card_lt
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)}
    {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
    (hvertices : 0 < vertices.card) : split.right.card < vertices.card := by
  have hbalance := split.right_balance
  omega
inductive BGKLSeparatorTree
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) : Finset ι → Type u
  | leaf (vertices : Finset ι) (small : vertices.card < d) :
      BGKLSeparatorTree P d vertices
  | branch {vertices : Finset ι} (split : BGKLSeparatorSplit P vertices)
      (large : d ≤ vertices.card)
      (leftTree : BGKLSeparatorTree P d split.left)
      (rightTree : BGKLSeparatorTree P d split.right) :
      BGKLSeparatorTree P d vertices
noncomputable def buildBGKLSeparatorTree
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (vertices : Finset ι) :
    BGKLSeparatorTree P d vertices := by
  classical
  by_cases hsmall : vertices.card < d
  · exact .leaf vertices hsmall
  · let split := minimumBGKLSeparatorSplit P vertices
    have hvertices : 0 < vertices.card := lt_of_lt_of_le hd (Nat.le_of_not_gt hsmall)
    exact .branch split (Nat.le_of_not_gt hsmall)
      (buildBGKLSeparatorTree P d hd split.left)
      (buildBGKLSeparatorTree P d hd split.right)
termination_by vertices.card
decreasing_by
  · exact split.left_card_lt hvertices
  · exact split.right_card_lt hvertices
noncomputable def fixedGeneratorOuterBoundaryFinset
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (vertices : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun q => decide
    (q ∈ P.fixedGeneratorOuterBoundary (vertices : Set ι))
def ancestorSeparatorUnion (separators : List (Finset ι)) : Finset ι :=
  separators.foldr (· ∪ ·) ∅
def ancestorSeparatorCardSum (separators : List (Finset ι)) : Nat :=
  (separators.map Finset.card).sum
inductive BGKLSeparatorTree.IsNode
    {P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)} {d : Nat} :
    {root : Finset ι} → BGKLSeparatorTree P d root →
      {node : Finset ι} → BGKLSeparatorTree P d node → List (Finset ι) → Prop
  | root {vertices : Finset ι} (tree : BGKLSeparatorTree P d vertices) :
      tree.IsNode tree []
  | left {vertices node : Finset ι} {ancestors : List (Finset ι)}
      (split : BGKLSeparatorSplit P vertices) (large : d ≤ vertices.card)
      (leftTree : BGKLSeparatorTree P d split.left)
      (rightTree : BGKLSeparatorTree P d split.right)
      (nodeTree : BGKLSeparatorTree P d node)
      (hnode : leftTree.IsNode nodeTree ancestors) :
      (BGKLSeparatorTree.branch split large leftTree rightTree).IsNode
        nodeTree (split.separator :: ancestors)
  | right {vertices node : Finset ι} {ancestors : List (Finset ι)}
      (split : BGKLSeparatorSplit P vertices) (large : d ≤ vertices.card)
      (leftTree : BGKLSeparatorTree P d split.left)
      (rightTree : BGKLSeparatorTree P d split.right)
      (nodeTree : BGKLSeparatorTree P d node)
      (hnode : rightTree.IsNode nodeTree ancestors) :
      (BGKLSeparatorTree.branch split large leftTree rightTree).IsNode
        nodeTree (split.separator :: ancestors)
noncomputable def bgklDecayRatio (exponent : ℝ) : ℝ :=
  Real.rpow (2 / 3 : ℝ) exponent
noncomputable def bgklSmallBoundaryEpsilon (beta exponent : ℝ) : ℝ :=
  (1 - bgklDecayRatio exponent) / (20 * beta)
end QEC.Locality


