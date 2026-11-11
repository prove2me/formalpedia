-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
-- name    : QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T11:00:55.694227+00:00
-- url     : https://prove2.me/theorems/7f7cd866-708e-4b77-9212-c7795da1b4c9
-- title:
--   Intervals
-- statement:
--   Definitions and structural lemmas for Intervals, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixEquiv_succ
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_stepEquiv_mk
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
namespace FC
export BDL26FiniteCohomology (Cocycle H1 classOf stepCocycle stepCocycle_value
  stepEquiv stepEquiv_mk prefixEquiv prefixEquiv_succ finiteH1Equiv generator)
end FC
variable (S : OddScale) (n : Nat)
def cocycleEdge (i : StepIndex n) :
    FC.Cocycle S (i.castSucc.val+2) →ₗ[BDL26Field] FC.Cocycle S (i.succ.val+2) :=
  FC.stepCocycle S (i.val+2)
def intervalCocycle (a b : LevelIndex n) (hab : a.val ≤ b.val) :
    FC.Cocycle S (a.val+2) →ₗ[BDL26Field] FC.Cocycle S (b.val+2) :=
  linearUp (V := fun i : LevelIndex n => ↥(FC.Cocycle S (i.val+2)))
    (cocycleEdge S n) b.val (Nat.le_of_lt_succ b.isLt) a hab
def suffixEquiv (a b : LevelIndex n) :
    FC.H1 S (a.val+2) ≃ₗ[BDL26Field] FC.H1 S (b.val+2) :=
  (FC.prefixEquiv S (a.val+2)).symm.trans (FC.prefixEquiv S (b.val+2))
def pureX (r : Nat) (v : FC.Cocycle S r) :
    BDL26LogicalQubitPreservation.DualRepresentative S r :=
  (BDL26LogicalQubitPreservation.cocycleEquiv S r).symm v
end QEC.Coding.BDL26HistoryLogicalResidual


