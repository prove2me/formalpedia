-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
-- name    : QEC_Coding_ExpanderCodes_LPSThetaFourier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:43:40.833969+00:00
-- url     : https://prove2.me/theorems/401bdee5-c2c9-4e59-9cf9-a1b9f9ccfd8a
-- title:
--   LPSTheta Fourier
-- statement:
--   Definitions and structural lemmas for LPSTheta Fourier, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaFourier.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Real
noncomputable def lpsQuadraticFourier (N : ℕ) [NeZero N] (a n : ZMod N) : ℂ :=
  ∑ r : ZMod N, ZMod.stdAddChar (a*r^2+n*r)
end QEC.Coding.TannerLiftedProduct


