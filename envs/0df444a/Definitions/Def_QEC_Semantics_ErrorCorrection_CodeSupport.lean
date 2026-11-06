-- Prove2me | Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
-- name    : QEC_Semantics_ErrorCorrection_CodeSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:56:33.811119+00:00
-- url     : https://prove2.me/theorems/f9609c36-162d-4d13-bec0-da6f69fde9b0
-- title:
--   Code Support
-- statement:
--   Definitions and structural lemmas for Code Support, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/CodeSupport.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped ComplexOrder
noncomputable section
namespace QuantumCode
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
noncomputable def projector (C : QuantumCode H) : Operator H :=
  C.carrier.starProjection.toLinearMap
end QuantumCode
namespace DensityOperator
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
noncomputable def pureOfNonzero (x : H) (hx : x ≠ 0) : DensityOperator H where
  toOperator :=
    (inner Complex x x)⁻¹ •
      (((InnerProductSpace.rankOne Complex x x : H →L[Complex] H) : H →ₗ[Complex] H))
  positive := by
    have hpos : LinearMap.IsPositive
        (((InnerProductSpace.rankOne Complex x x : H →L[Complex] H) : H →ₗ[Complex] H)) := by
      exact (InnerProductSpace.isPositive_rankOne_self (𝕜 := Complex) x).toLinearMap
    have hinner_nonneg : 0 ≤ inner Complex x x := by
      rw [inner_self_eq_norm_sq_to_K]
      positivity
    exact hpos.smul_of_nonneg ((inv_nonneg).2 hinner_nonneg)
  trace_one := by
    rw [map_smul, InnerProductSpace.trace_rankOne]
    exact inv_mul_cancel₀ (inner_self_ne_zero.mpr hx)
end DensityOperator
end
end Semantics
end QEC


