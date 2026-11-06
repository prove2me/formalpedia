-- Prove2me | Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
-- name    : QEC_Semantics_Core_OperatorTraceNorm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:04:56.580777+00:00
-- url     : https://prove2.me/theorems/edadbcf1-87e5-47b2-859c-99949fc205dd
-- title:
--   Operator Trace Norm
-- statement:
--   Definitions and structural lemmas for Operator Trace Norm, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
def operatorNorm (A : Operator H) : Real :=
  ‖LinearMap.toContinuousLinearMap A‖
def tracePairing (A : Operator H) : (H →L[Complex] H) →L[Complex] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => LinearMap.trace Complex H (B.toLinearMap * A)
      map_add' := by
        intro B C
        simp [add_mul]
      map_smul' := by
        intro c B
        simp }
def traceNorm (A : Operator H) : Real :=
  ‖tracePairing A‖
namespace DensityOperator
end DensityOperator
noncomputable def positivePart (A : Operator H) : Operator H :=
  ((LinearMap.toContinuousLinearMap A)⁺).toLinearMap
noncomputable def negativePart (A : Operator H) : Operator H :=
  ((LinearMap.toContinuousLinearMap A)⁻).toLinearMap
noncomputable def positiveSupportProjection (A : Operator H) : H →L[Complex] H :=
  ((LinearMap.toContinuousLinearMap A)⁺).range.starProjection
noncomputable def negativeSupportProjection (A : Operator H) : H →L[Complex] H :=
  ((LinearMap.toContinuousLinearMap A)⁻).range.starProjection
noncomputable def spectralSign (A : Operator H) : H →L[Complex] H :=
  positiveSupportProjection A - negativeSupportProjection A
def projectedTail (P A : Operator H) : Operator H :=
  (1 - P) * A * (1 - P)
namespace DensityOperator
end DensityOperator
end
end Semantics
end QEC


