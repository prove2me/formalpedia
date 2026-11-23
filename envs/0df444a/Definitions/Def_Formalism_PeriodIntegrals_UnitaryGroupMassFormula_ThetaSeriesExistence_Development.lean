-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:13.111647+00:00
-- url     : https://prove2.me/theorems/8a087e2d-1dcf-47c8-addf-6b61fc7d47af
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesExistence/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
import Definitions.Def_Formalism_PeriodIntegrals_SigmaStarEx
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
namespace PI.SSE
def ThetaA : Prop :=
  ∀ τ : ℂ, 0 < τ.im → Differentiable ℂ (th τ) ∧ (∀ u, th τ (-u) = -th τ u) ∧
    (∀ u, th τ (u + 1) = -th τ u) ∧
    (∀ u, th τ (u + τ) = -(cexp (-(Real.pi * I * τ) - 2 * Real.pi * I * u) * th τ u)) ∧
    deriv (th τ) 0 = jacobiTheta₂' (1 / 2 + τ / 2) τ
def qf (A ω z : ℂ) : ℂ := cexp (Real.pi * (starRingEnd ℂ) ω * (z + ω / 2) / A)
def GenEq : Prop :=
  ∀ v₁ v₂ : ℂ, v₁ ≠ 0 → 0 < (v₂ / v₁).im → 3 ≤ 4 * (v₂ / v₁).im ^ 2 →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      (∀ z, G (z + v₁) = -(qf (((starRingEnd ℂ) v₁ * v₂).im) v₁ z * G z)) ∧
      (∀ z, G (z + v₂) = -(qf (((starRingEnd ℂ) v₁ * v₂).im) v₂ z * G z))
def LatExt : Prop :=
  ∀ v₁ v₂ : ℂ, 0 < ((starRingEnd ℂ) v₁ * v₂).im → ∀ G : ℂ → ℂ,
    (∀ z, G (z + v₁) = -(qf (((starRingEnd ℂ) v₁ * v₂).im) v₁ z * G z)) →
    (∀ z, G (z + v₂) = -(qf (((starRingEnd ℂ) v₁ * v₂).im) v₂ z * G z)) →
    ∀ ω ∈ PI.lat2 v₁ v₂, ∀ z, G (z + ω) =
      (if ω / 2 ∈ PI.lat2 v₁ v₂ then 1 else -1) * (qf (((starRingEnd ℂ) v₁ * v₂).im) ω z * G z)
def GenEqOf : Prop := ThetaA → ThetaDerivNe → GenEq
end PI.SSE
end


