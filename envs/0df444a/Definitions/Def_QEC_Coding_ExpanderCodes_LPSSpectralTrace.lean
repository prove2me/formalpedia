-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
-- name    : QEC_Coding_ExpanderCodes_LPSSpectralTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:20:43.785209+00:00
-- url     : https://prove2.me/theorems/838c45c5-c07f-4dc6-aa68-b55ac0d9ee9d
-- title:
--   LPSSpectral Trace
-- statement:
--   Definitions and structural lemmas for LPSSpectral Trace, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSpectralTrace.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMomentBound
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
set_option autoImplicit false
open Filter Asymptotics
open Polynomial
namespace QEC.Coding.TannerLiftedProduct
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
end QEC.Coding.TannerLiftedProduct


