-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:22.574583+00:00
-- url     : https://prove2.me/theorems/fc0c1c9c-ca2c-5a25-9483-5de25932383a
-- title:
--   Differentiable Odd Theta
-- statement:
--   Definitions and structural lemmas for Differentiable Odd Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DifferentiableOddTheta.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
namespace GlobalTheory.ThetaWeberRoad
def tpFactor (τ : ℍ) (z : ℂ) (n : ℕ) : ℂ :=
  (1 - cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ))) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * z)) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * z))
def TripleProduct : Prop := ∀ (τ : ℍ) (z : ℂ), HasProd (tpFactor τ z) (jacobiTheta₂ z τ)
def oddTheta (τ : ℍ) (z : ℂ) : ℂ :=
  cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) * jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ
end GlobalTheory.ThetaWeberRoad


