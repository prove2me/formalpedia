-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
-- name    : QEC_Coding_ExpanderCodes_LPSThetaIntegralLattice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:34:53.960245+00:00
-- url     : https://prove2.me/theorems/a4f46c40-cde1-4150-bfe6-b5cf1db7e468
-- title:
--   LPSTheta Integral Lattice
-- statement:
--   Definitions and structural lemmas for LPSTheta Integral Lattice, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaIntegralLattice.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
def lpsThetaIntegerDenominator (q : ℕ) : ℤ := 48*(q : ℤ)^2*((q : ℤ)^2-1)
end
end QEC.Coding.TannerLiftedProduct


