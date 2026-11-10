-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
-- name    : QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T05:30:23.0202+00:00
-- url     : https://prove2.me/theorems/37427dd1-c8e2-436f-bdb2-cff97050c4f2
-- title:
--   Logical Qubit Preservation
-- statement:
--   Definitions and structural lemmas for Logical Qubit Preservation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LogicalQubitPreservation.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26LogicalQubitPreservation
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge MultiscaleDecoder
open scoped Classical
abbrev Field := ZMod 2
noncomputable abbrev complex := BDL26FiniteCohomology.complex
noncomputable abbrev DualRepresentative (S : OddScale) (n : Nat) :=
  (complex S n).middleBoundaryCode.dual.carrier
noncomputable abbrev LogicalQuotient (S : OddScale) (n : Nat) :=
  (complex S n).pureXLogicalQuotient
noncomputable abbrev logicalClass (S : OddScale) (n : Nat) :
    DualRepresentative S n →ₗ[Field] LogicalQuotient S n :=
  (complex S n).firstCoboundaryInMiddleBoundaryDual.mkQ
noncomputable abbrev cocycleEquiv (S : OddScale) (n : Nat) :
    DualRepresentative S n ≃ₗ[Field] BDL26FiniteCohomology.Cocycle S n :=
  (complex S n).middleBoundaryDualEquivMiddleCocycleCode
noncomputable abbrev logicalToH1 (S : OddScale) (n : Nat) :
    LogicalQuotient S n ≃ₗ[Field] BDL26FiniteCohomology.H1 S n :=
  (complex S n).pureXLogicalQuotientEquivMiddleCohomology
noncomputable def logicalEquiv (S : OddScale) (n : Nat) :
    LogicalQuotient S n ≃ₗ[Field] Field :=
  (logicalToH1 S n).trans (BDL26FiniteCohomology.finiteH1Equiv S n)
noncomputable def prefixRepresentative (S : OddScale) (n : Nat)
    (w : BDL26FiniteCohomology.Cocycle S 0) : DualRepresentative S n :=
  (cocycleEquiv S n).symm (BDL26FiniteCohomology.prefixCocycle S n w)
noncomputable def logicalStepEquiv (S : OddScale) (n : Nat) :
    LogicalQuotient S n ≃ₗ[Field] LogicalQuotient S (n+1) :=
  ((logicalToH1 S n).trans (BDL26FiniteCohomology.stepEquiv S n)).trans
    (logicalToH1 S (n+1)).symm
noncomputable def stepRepresentative (S : OddScale) (n : Nat)
    (w : DualRepresentative S n) : DualRepresentative S (n+1) :=
  (cocycleEquiv S (n+1)).symm
    (BDL26FiniteCohomology.stepCocycle S n (cocycleEquiv S n w))
noncomputable def indexedLogicalEquiv (S : OddScale) (depth : Nat) (i : LevelIndex depth) :
    ((indexedFamily S depth).complex i).pureXLogicalQuotient ≃ₗ[Field] Field :=
  logicalEquiv S i.val
noncomputable def indexedLogicalStepEquiv (S : OddScale) (depth : Nat) (i : StepIndex depth) :
    ((indexedFamily S depth).complex i.castSucc).pureXLogicalQuotient ≃ₗ[Field]
      ((indexedFamily S depth).complex i.succ).pureXLogicalQuotient :=
  logicalStepEquiv S i.val
end QEC.Coding.BDL26LogicalQubitPreservation


