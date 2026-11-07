-- Prove2me | Definitions.Def_QEC_Locality_ConnectivityTradeoff_TwoPassDimension
-- name    : QEC_Locality_ConnectivityTradeoff_TwoPassDimension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:49:03.849881+00:00
-- url     : https://prove2.me/theorems/c071dd58-bdd3-4db4-93bf-2e0a7196da16
-- title:
--   Two Pass Dimension
-- statement:
--   Definitions and structural lemmas for Two Pass Dimension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/TwoPassDimension.lean

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open QEC Semantics Locality
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
def bkPartitionRegion {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) : FiniteSubsystem ι :=
  ⟨partition.pieces.biUnion id⟩
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
namespace QEC.Locality
universe u v
namespace BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]
end BKQLDPCFamily
end QEC.Locality


