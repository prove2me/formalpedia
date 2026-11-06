-- Prove2me | Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
-- name    : QEC_Locality_SeparatorProfile_Weighted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:15:33.724202+00:00
-- url     : https://prove2.me/theorems/8fd3b73c-9a11-4717-9ffd-6fcadf7c29d9
-- title:
--   Weighted
-- statement:
--   Definitions and structural lemmas for Weighted, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/SeparatorProfile/Weighted.lean

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Theorems.Thm_QEC_Locality_measuredTwoThirdsLeft_subset
import Theorems.Thm_QEC_Locality_measuredTwoThirdsRight_subset
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
inductive MarkedSeparatorSpine (G : ConnectivityGraph ι) (marked : Finset ι) :
    Finset ι → Type u
  | stop {vertices left separator right : Finset ι}
      (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
      (hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
      (hleftLight : 3 * (marked ∩ left).card ≤ 2 * marked.card)
      (hrightLight : 3 * (marked ∩ right).card ≤ 2 * marked.card) :
      MarkedSeparatorSpine G marked vertices
  | followLeft {vertices left separator right : Finset ι}
      (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
      (hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
      (hleftHeavy : 2 * marked.card < 3 * (marked ∩ left).card)
      (subtree : MarkedSeparatorSpine G marked left) :
      MarkedSeparatorSpine G marked vertices
  | followRight {vertices left separator right : Finset ι}
      (hpartition : TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right)
      (hminimum : separator.card =
        minimumTwoThirdsBalancedVertexSeparatorSize G vertices)
      (hrightHeavy : 2 * marked.card < 3 * (marked ∩ right).card)
      (subtree : MarkedSeparatorSpine G marked right) :
      MarkedSeparatorSpine G marked vertices
noncomputable def MarkedSeparatorSpine.separators
    {G : ConnectivityGraph ι} {marked vertices : Finset ι} :
    MarkedSeparatorSpine G marked vertices → List (Finset ι)
  | @stop _ _ _ _ _ vertices left separator right hpartition hminimum hleftLight hrightLight =>
      [separator]
  | @followLeft _ _ _ _ _ vertices left separator right hpartition hminimum hleftHeavy subtree =>
      separator :: subtree.separators
  | @followRight _ _ _ _ _ vertices left separator right hpartition hminimum hrightHeavy subtree =>
      separator :: subtree.separators
noncomputable def MarkedSeparatorSpine.stopSides
    {G : ConnectivityGraph ι} {marked vertices : Finset ι} :
    MarkedSeparatorSpine G marked vertices → Finset ι × Finset ι
  | @stop _ _ _ _ _ vertices left separator right hpartition hminimum hleftLight hrightLight =>
      (left, right)
  | @followLeft _ _ _ _ _ vertices left separator right hpartition hminimum hleftHeavy subtree =>
      subtree.stopSides
  | @followRight _ _ _ _ _ vertices left separator right hpartition hminimum hrightHeavy subtree =>
      subtree.stopSides
noncomputable def MarkedSeparatorSpine.exposedSide
    {G : ConnectivityGraph ι} {marked vertices : Finset ι} :
    MarkedSeparatorSpine G marked vertices → Finset ι
  | .stop _ _ _ _ => ∅
  | @followLeft _ _ _ _ _ vertices left separator right hpartition hminimum hleftHeavy subtree =>
      right ∪ subtree.exposedSide
  | @followRight _ _ _ _ _ vertices left separator right hpartition hminimum hrightHeavy subtree =>
      left ∪ subtree.exposedSide
noncomputable def MarkedSeparatorSpine.terminalCarrier
    {G : ConnectivityGraph ι} {marked vertices : Finset ι} :
    MarkedSeparatorSpine G marked vertices → Finset ι
  | .stop _ _ _ _ => vertices
  | .followLeft _ _ _ subtree => subtree.terminalCarrier
  | .followRight _ _ _ subtree => subtree.terminalCarrier
noncomputable def markedSpineSeparatorCardSum
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) : Nat :=
  (spine.separators.map Finset.card).sum
noncomputable def markedSpineSeparatorUnion
    {G : ConnectivityGraph ι} {marked vertices : Finset ι}
    (spine : MarkedSeparatorSpine G marked vertices) : Finset ι :=
  spine.separators.foldr (· ∪ ·) ∅
noncomputable def markedSpineDecayRatio (exponent : ℝ) : ℝ :=
  Real.rpow (2 / 3 : ℝ) exponent
noncomputable def weightedSpineSeparatorBudget
    (beta exponent : ℝ) (r : Nat) : Nat :=
  Nat.ceil (beta / (1 - markedSpineDecayRatio exponent) * Real.rpow r exponent)
noncomputable def weightedProfileBoundaryBudget
    (beta exponent : ℝ) (r : Nat) : Nat :=
  6 * weightedSpineSeparatorBudget beta exponent r
theorem measured_left_card_lt
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (hpositive : 0 < vertices.card) :
    (measuredTwoThirdsLeft G vertices).card < vertices.card := by
  have hnonempty : vertices.Nonempty := Finset.card_pos.mp hpositive
  exact measuredTwoThirdsLeft_card_lt G vertices hnonempty
theorem measured_right_card_lt
    (G : ConnectivityGraph ι) (vertices : Finset ι)
    (hpositive : 0 < vertices.card) :
    (measuredTwoThirdsRight G vertices).card < vertices.card := by
  have hnonempty : vertices.Nonempty := Finset.card_pos.mp hpositive
  exact measuredTwoThirdsRight_card_lt G vertices hnonempty
noncomputable def buildMarkedSeparatorSpine
    (G : ConnectivityGraph ι) (marked vertices : Finset ι) :
    MarkedSeparatorSpine G marked vertices := by
  classical
  let left := measuredTwoThirdsLeft G vertices
  let separator := measuredTwoThirdsSeparator G vertices
  let right := measuredTwoThirdsRight G vertices
  have hpartition :
      TwoThirdsBalancedPartitionAfterDeleting G vertices left separator right :=
    measuredTwoThirdsSplit_spec G vertices
  have hminimum : separator.card =
      minimumTwoThirdsBalancedVertexSeparatorSize G vertices :=
    (measuredTwoThirdsSeparator_spec G vertices).2.2
  by_cases hleftHeavy : 2 * marked.card < 3 * (marked ∩ left).card
  · have hleftPositive : 0 < left.card := by
      have : 0 < (marked ∩ left).card := by omega
      exact this.trans_le (Finset.card_le_card Finset.inter_subset_right)
    exact .followLeft hpartition hminimum hleftHeavy
      (buildMarkedSeparatorSpine G marked left)
  · by_cases hrightHeavy : 2 * marked.card < 3 * (marked ∩ right).card
    · have hrightPositive : 0 < right.card := by
        have : 0 < (marked ∩ right).card := by omega
        exact this.trans_le (Finset.card_le_card Finset.inter_subset_right)
      exact .followRight hpartition hminimum hrightHeavy
        (buildMarkedSeparatorSpine G marked right)
    · refine .stop hpartition hminimum ?_ ?_
      · omega
      · omega
termination_by vertices.card
decreasing_by
  · apply measured_left_card_lt G vertices
    exact hleftPositive.trans_le
      (Finset.card_le_card (measuredTwoThirdsLeft_subset G vertices))
  · apply measured_right_card_lt G vertices
    exact hrightPositive.trans_le
      (Finset.card_le_card (measuredTwoThirdsRight_subset G vertices))
end QEC.Locality


