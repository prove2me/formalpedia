-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
-- name    : QEC_Coding_ExpanderCodes_LPSCuspDifferential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:17:40.148333+00:00
-- url     : https://prove2.me/theorems/35f5925e-c27f-4116-90a9-2af2264acc99
-- title:
--   LPSCusp Differential
-- statement:
--   Definitions and structural lemmas for LPSCusp Differential, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspDifferential.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.Analysis.Normed.Operator.Mul
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section
def lpsCuspDifferential (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) : ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ (f τ)
end
end QEC.Coding.TannerLiftedProduct


