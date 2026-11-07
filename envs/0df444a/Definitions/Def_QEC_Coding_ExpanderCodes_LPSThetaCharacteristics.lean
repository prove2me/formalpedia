-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
-- name    : QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:41:34.267681+00:00
-- url     : https://prove2.me/theorems/7ff8f6fa-1fdc-4140-b935-2c8e38824b0c
-- title:
--   LPSTheta Characteristics
-- statement:
--   Definitions and structural lemmas for LPSTheta Characteristics, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCharacteristics.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaS
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Real Filter Topology
noncomputable def lpsShiftedTheta (a z : ℂ) : ℂ :=
  Complex.exp ((Real.pi:ℂ)*Complex.I*a^2*z) * jacobiTheta₂ (a*z) z
noncomputable def lpsQuadraticPhase (a : ℤ) (c : ℕ) (r : Fin c) : ℂ :=
  Complex.exp (2*(Real.pi:ℂ)*Complex.I*(a:ℂ)*(r.val:ℂ)^2/(c:ℂ))
noncomputable def lpsUnaryQuadraticGauss (a : ℤ) (c : ℕ) : ℂ := ∑ r : Fin c, lpsQuadraticPhase a c r
noncomputable def lpsThetaGaussSum (a : ℤ) (c : ℕ) (z : ℂ) : ℂ :=
  ∑ r : Fin c, lpsQuadraticPhase a c r * jacobiTheta₂ ((r.val:ℂ)/(c:ℂ)) z
end QEC.Coding.TannerLiftedProduct


