-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
-- name    : QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:52:21.800905+00:00
-- url     : https://prove2.me/theorems/13f98b36-c136-4551-b726-fccb4318224b
-- title:
--   Finite Measurement Distance
-- statement:
--   Definitions and structural lemmas for Finite Measurement Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_smul

set_option autoImplicit false
noncomputable section
namespace QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)
def fullRegion : QuditSubsystem q := ⟨Finset.univ⟩
def fullRegionLabelEquiv : Qudit.Label (fun j : (fullRegion q).SelectedCoordinates => q j.val) ≃
    Qudit.Label q where
  toFun x j := x ⟨j, Finset.mem_univ j⟩
  invFun x j := x j.val
  left_inv x := by funext j; rfl
  right_inv x := rfl
def extensionLinearMap (S : QuditSubsystem q) :
    Operator S.selectedSystem →ₗ[Complex] Operator (Qudit.QuditRegister q) where
  toFun := S.extendLocalToRegister
  map_add' := S.extendLocalToRegister_add
  map_smul' := S.extendLocalToRegister_smul
def finiteMeasurementDistance (C : QuantumCode (Qudit.QuditRegister q)) : Nat :=
  sInf {d : Nat | ¬ BPTMeasurementDistance C (d + 1)}
end QEC.Semantics.QuditSubsystem


