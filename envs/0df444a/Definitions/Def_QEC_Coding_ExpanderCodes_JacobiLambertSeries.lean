-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
-- name    : QEC_Coding_ExpanderCodes_JacobiLambertSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:17:29.064627+00:00
-- url     : https://prove2.me/theorems/fa7e56a1-7278-486a-bad2-8a3617cf3712
-- title:
--   Jacobi Lambert Series
-- statement:
--   Definitions and structural lemmas for Jacobi Lambert Series, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
noncomputable def jacobiGeometricSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun _ => 1
noncomputable def jacobiMinusLogDerivative (d : ℕ) : ℚ⟦X⟧ :=
  -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
    jacobiGeometricSeries.subst (PowerSeries.X ^ d))
noncomputable def jacobiPlusLogDerivative (d : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
    jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))
noncomputable def jacobiThetaLogDerivativeSummand (n : ℕ) : ℚ⟦X⟧ :=
  jacobiMinusLogDerivative (2 * (n + 1)) +
    2 * jacobiPlusLogDerivative (2 * n + 1)
noncomputable def jacobiThetaLogDerivative : ℚ⟦X⟧ :=
  ∑' n, jacobiThetaLogDerivativeSummand n
noncomputable def jacobiTriangularLogDerivativeSummand (n : ℕ) : ℚ⟦X⟧ :=
  jacobiMinusLogDerivative (2 * (n + 1)) +
    2 * jacobiPlusLogDerivative (2 * (n + 1))
noncomputable def jacobiTriangularLogDerivative : ℚ⟦X⟧ :=
  ∑' n, jacobiTriangularLogDerivativeSummand n
noncomputable def jacobiLogDerivativeDifference : ℚ⟦X⟧ :=
  jacobiTriangularLogDerivative - jacobiThetaLogDerivative
noncomputable def jacobiLambertTerm (d : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if 0 < n ∧ d ∣ n then d else 0
noncomputable def jacobiLambertSeries : ℚ⟦X⟧ :=
  1 + PowerSeries.C 8 *
    ∑' d : ℕ, if 4 ∣ d then 0 else jacobiLambertTerm d
noncomputable def rationalJacobiFourSquareSeries : ℚ⟦X⟧ :=
  PowerSeries.map (Nat.castRingHom ℚ) jacobiFourSquareSeries
end QEC.Coding.TannerLiftedProduct


