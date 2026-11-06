-- Prove2me | Definitions.Def_QEC_Locality_CorrectablePartition_Core
-- name    : QEC_Locality_CorrectablePartition_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:01:35.516628+00:00
-- url     : https://prove2.me/theorems/c81fb9f8-7811-442b-8b8c-64c4b566b94f
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectablePartition/Core.lean

import Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
noncomputable def explicitDivisionInterior
    {G : ConnectivityGraph ι} {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap)
    (owner : division.Owner) : Finset ι := by
  letI := division.ownerDecidableEq
  exact edgeDivisionInterior division.region division.active owner
noncomputable def explicitDivisionSharedBoundary
    {G : ConnectivityGraph ι} {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap) : Finset ι := by
  letI := division.ownerDecidableEq
  exact edgeDivisionSharedBoundary division.region division.active
noncomputable def explicitDivisionLocalBoundary
    {G : ConnectivityGraph ι} {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap)
    (owner : division.Owner) : Finset ι := by
  letI := division.ownerDecidableEq
  exact edgeIncidentVertices (division.region owner) ∩ explicitDivisionSharedBoundary division
noncomputable def explicitDivisionPiece
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap) :
    division.Owner ⊕ ι → FiniteSubsystem ι
  | .inl owner => finiteSubsystemOfFinset (explicitDivisionInterior division owner)
  | .inr vertex => finiteSubsystemOfFinset {vertex}
noncomputable def explicitDivisionPieceActive
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap) :
    Finset (division.Owner ⊕ ι) := by
  classical
  exact division.active.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (graphIsolatedVertices G).map ⟨Sum.inr, Sum.inr_injective⟩
noncomputable def explicitDivisionCorrectableUnion
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap) :
    FiniteSubsystem ι :=
  familyUnionSubsystem (explicitDivisionPiece G division)
    (explicitDivisionPieceActive G division)
noncomputable def bgklPartitionBoundaryCoefficient (beta exponent : ℝ) : ℝ :=
  beta / (1 - markedSpineDecayRatio exponent)
noncomputable def bgklPartitionEpsilon (beta exponent : ℝ) : ℝ :=
  min (bgklSmallBoundaryEpsilon beta exponent)
    (1 / (96 * bgklPartitionBoundaryCoefficient beta exponent))
noncomputable def bgklPartitionScaleTarget (beta exponent : ℝ) (d : Nat) : ℝ :=
  Real.rpow (bgklPartitionEpsilon beta exponent * d) exponent⁻¹
noncomputable def bgklPartitionScale (beta exponent : ℝ) (d : Nat) : Nat :=
  Nat.floor (bgklPartitionScaleTarget beta exponent d)
noncomputable def bgklPartitionSmallCutoff (beta exponent : ℝ) : ℝ :=
  max 96 (Real.rpow (max 2 (profileDivisionThreshold beta exponent)) exponent /
    bgklPartitionEpsilon beta exponent)
noncomputable def bgklPartitionAlpha (beta exponent : ℝ) : ℝ :=
  1 + Real.rpow (bgklPartitionSmallCutoff beta exponent) ((1 - exponent) / exponent) +
    (profileDivisionRegionConstant beta exponent + 1) *
      Real.rpow (bgklPartitionEpsilon beta exponent) (-exponent⁻¹)
end QEC.Locality


