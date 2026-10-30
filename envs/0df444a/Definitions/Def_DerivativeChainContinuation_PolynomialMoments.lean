-- Prove2me | Definitions.Def_DerivativeChainContinuation_PolynomialMoments
-- name    : DerivativeChainContinuation_PolynomialMoments
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:02:56.807595+00:00
-- url     : https://prove2.me/theorems/16fc1152-e45d-402c-9717-46a90cadbece
-- title:
--   Monic normalized derivative
-- statement:
--   Define the monic normalized derivative of a complex polynomial by dividing its derivative by the source degree. For a positive-degree monic source this is the actual derivative with leading coefficient normalized to one.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PolynomialMoments.lean#L6-L7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

noncomputable def monicDerivative (p : Polynomial ℂ) : Polynomial ℂ :=
  C (p.natDegree : ℂ)⁻¹ * p.derivative










end DerivativeChainContinuation


