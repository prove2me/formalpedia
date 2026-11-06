-- Prove2me | Definitions.Def_QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement
-- name    : QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:47:27.189077+00:00
-- url     : https://prove2.me/theorems/cff36638-b313-4081-9119-b915bcc25d40
-- title:
--   Filtered Branch Measurement
-- statement:
--   Definitions and structural lemmas for Filtered Branch Measurement, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/FilteredBranchMeasurement.lean

import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
set_option autoImplicit false
noncomputable section
namespace QEC
namespace Semantics
namespace FiniteInstrument
open Classical
open scoped BigOperators
universe u v w x y
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {mu : Type x} [Fintype mu]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]
end FiniteInstrument
end Semantics
end QEC


