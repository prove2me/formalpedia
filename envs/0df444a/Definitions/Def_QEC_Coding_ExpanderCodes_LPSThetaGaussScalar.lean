-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
-- name    : QEC_Coding_ExpanderCodes_LPSThetaGaussScalar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:48:26.901058+00:00
-- url     : https://prove2.me/theorems/db068c0a-703a-4cf7-99ad-5f1b67b3bf48
-- title:
--   LPSTheta Gauss Scalar
-- statement:
--   Definitions and structural lemmas for LPSTheta Gauss Scalar, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaGaussScalar.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups
noncomputable def lpsThetaPositiveGaussScalar (q : ℕ) (γ : SL(2,ℤ)) : ℂ :=
  -(32*(q:ℂ)^3*((γ 1 0).toNat:ℂ)^2)⁻¹ *
    lpsUnaryQuadraticGauss (γ 0 0) (γ 1 0).toNat *
    lpsUnaryQuadraticGauss (4*(q:ℤ)^2*γ 0 0) (γ 1 0).toNat^3
noncomputable def lpsThetaGammaGaussScalar (q : ℕ) (γ : SL(2,ℤ)) : ℂ :=
  if γ 1 0=0 then 1 else
    if 0 < γ 1 0 then lpsThetaPositiveGaussScalar q γ else lpsThetaPositiveGaussScalar q (-γ)
end QEC.Coding.TannerLiftedProduct


