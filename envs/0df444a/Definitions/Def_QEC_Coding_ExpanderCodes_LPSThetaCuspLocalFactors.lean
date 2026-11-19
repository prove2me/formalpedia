-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
-- name    : QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:34:05.400556+00:00
-- url     : https://prove2.me/theorems/f8f7e070-2d34-4877-8375-4537e8868c3b
-- title:
--   LPSTheta Cusp Local Factors
-- statement:
--   Definitions and structural lemmas for LPSTheta Cusp Local Factors, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable def lpsThetaCuspGaussProduct (q : ℕ) (a : ℤ) (N : ℕ) : ℂ :=
  lpsUnaryQuadraticGauss a N*lpsUnaryQuadraticGauss (4*(q:ℤ)^2*a) N^3
end QEC.Coding.TannerLiftedProduct


