-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
-- name    : QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:35:26.421723+00:00
-- url     : https://prove2.me/theorems/e3b565d1-908e-4fb1-8fb3-0485574933ff
-- title:
--   LPSTheta Eisenstein Cusps
-- statement:
--   Definitions and structural lemmas for LPSTheta Eisenstein Cusps, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable def lpsThetaEisensteinTwoCuspFactor (γ : SL(2,ℤ)) : ℂ :=
  ∑ a : Fin 5,lpsThetaEisensteinTwoWeight a*
    (Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)
noncomputable def lpsThetaEisensteinPrimeCuspFactor (q : ℕ) (γ : SL(2,ℤ)) : ℂ :=
  ∑ b : Fin 3,lpsThetaEisensteinPrimeWeight q b*
    (Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)
end QEC.Coding.TannerLiftedProduct


