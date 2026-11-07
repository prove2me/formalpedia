-- Prove2me | Definitions.Def_QEC_Results_LocalityBounds_RestrictedConnectivity
-- name    : QEC_Results_LocalityBounds_RestrictedConnectivity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:59:27.216407+00:00
-- url     : https://prove2.me/theorems/7e801534-9478-43e7-b3d1-e79dd0da0a0c
-- title:
--   Restricted Connectivity
-- statement:
--   Definitions and structural lemmas for Restricted Connectivity, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/LocalityBounds/RestrictedConnectivity.lean

import Definitions.Def_QEC_Locality_CorrectablePartition_Core
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
set_option autoImplicit false
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def bgklBKPartitionRegion
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) : FiniteSubsystem ι :=
  ⟨partition.pieces.biUnion id⟩
structure BGKLRestrictedConnectivityFamily
    (ι : Nat → Type u) (κ : Nat → Type v)
    [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)] where
  validIndex : Nat → Prop
  parameterData : ∀ n, StabilizerCode.StabilizerParameterData (ι := ι n) (κ := κ n)
  blockLength_eq_index : ∀ n, validIndex n → (parameterData n).blockLength = n
  distance_pos : ∀ n, validIndex n → 1 ≤ (parameterData n).distance
  distance_le_index : ∀ n, validIndex n → (parameterData n).distance ≤ n
namespace BGKLRestrictedConnectivityFamily
variable {ι : Nat → Type u} {κ : Nat → Type v}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] [∀ n, Fintype (κ n)]
abbrev Index (family : BGKLRestrictedConnectivityFamily ι κ) :=
  {n : Nat // family.validIndex n}
end BGKLRestrictedConnectivityFamily
end QEC.Locality


