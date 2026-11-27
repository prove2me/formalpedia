-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-27T05:19:19.243624+00:00
-- url     : https://prove2.me/theorems/22406a94-6ef1-4890-a6ee-5132bd3cb1dc
-- title:
--   Theta Constant Weber
-- statement:
--   Definitions and structural lemmas for Theta Constant Weber, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/ThetaConstantWeber.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
def thetaConst (a b : ℕ) (τ : ℍ) : ℂ :=
  cexp (π * I * (a : ℂ) ^ 2 * (τ : ℂ) / 4 + π * I * a * b / 2) *
    jacobiTheta₂ (((a : ℂ) * (τ : ℂ) + b) / 2) τ
def weberF (τ : ℍ) : ℂ :=
  cexp (-(π * I / 24)) * ModularForm.eta (((τ : ℂ) + 1) / 2) / ModularForm.eta τ
def weberF₁ (τ : ℍ) : ℂ := ModularForm.eta ((τ : ℂ) / 2) / ModularForm.eta τ
def weberF₂ (τ : ℍ) : ℂ := (√2 : ℝ) * ModularForm.eta (2 * (τ : ℂ)) / ModularForm.eta τ
def wp (τ : ℍ) (z : ℂ) : ℂ := (periodPairOfTau τ).weierstrassP z
def jLat (τ : ℍ) : ℂ := (latticeCurve (periodPairOfTau τ)).j
def HalfPeriodDiff (τ : ℍ) : Prop :=
  wp τ (1 / 2) - wp τ ((τ : ℂ) / 2) = (π : ℂ) ^ 2 * thetaConst 0 0 τ ^ 4 ∧
  wp τ (1 / 2) - wp τ ((1 + (τ : ℂ)) / 2) = (π : ℂ) ^ 2 * thetaConst 0 1 τ ^ 4 ∧
  wp τ ((1 + (τ : ℂ)) / 2) - wp τ ((τ : ℂ) / 2) = (π : ℂ) ^ 2 * thetaConst 1 0 τ ^ 4
def JacobiProduct (τ : ℍ) : Prop :=
  thetaConst 0 0 τ * thetaConst 0 1 τ * thetaConst 1 0 τ = 2 * ModularForm.eta τ ^ 3
def ThetaWeber (τ : ℍ) : Prop :=
  thetaConst 0 0 τ = ModularForm.eta τ * weberF τ ^ 2 ∧
  thetaConst 0 1 τ = ModularForm.eta τ * weberF₁ τ ^ 2 ∧
  thetaConst 1 0 τ = ModularForm.eta τ * weberF₂ τ ^ 2
def WeberCubic (τ : ℍ) : Prop :=
  ((X - C 16) ^ 3 - C (jLat τ) * X : ℂ[X]) =
    (X - C (weberF τ ^ 24)) * (X - C (-weberF₁ τ ^ 24)) * (X - C (-weberF₂ τ ^ 24))
def ThetaWeberStatement : Prop :=
  ∀ τ : ℍ, HalfPeriodDiff τ ∧ JacobiProduct τ ∧ ThetaWeber τ ∧ WeberCubic τ
example (τ : ℍ) : thetaConst 0 0 τ = jacobiTheta τ := by
  simp [thetaConst, jacobiTheta_eq_jacobiTheta₂]
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber


