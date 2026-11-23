-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesUniqueness_Complete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:18.0468+00:00
-- url     : https://prove2.me/theorems/2a6b40b6-2911-47fc-9ef0-39a4a1a1e9d9
-- title:
--   Complete
-- statement:
--   Definitions and structural lemmas for Complete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ThetaSeriesUniqueness/Complete.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
import Definitions.Def_Formalism_PeriodIntegrals_SigmaStarUniq
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.SSU
open Complex
def coef (f : ℂ → ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0:ℝ)..1, f x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x))
def ShiftInv : Prop := ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ u, f (u + 1) = f u) →
  ∀ (w : ℂ) (n : ℤ),
    (∫ x in (0:ℝ)..1, f (x + w) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (x + w)))) = coef f n
def Complete : Prop := ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ u, f (u + 1) = f u) →
  (∀ n, coef f n = 0) → f = 0
def KeyP : Prop := ∀ (f : ℂ → ℂ) (τ K : ℂ) (k : ℤ), Differentiable ℂ f → K ≠ 0 →
  (k = 1 ∨ k = -1) → (∀ u, f (u + 1) = f u) →
  (∀ u, f (u + τ) = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * k * u)) * f u) → coef f 0 = 0 → f = 0
def FE (A ω p : ℂ) (F : ℂ → ℂ) : Prop := ∀ z, F (z + ω) * Complex.exp
    (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / A - (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * A)) =
    p * F z
def normF (a A l : ℂ) (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  F (a * u) * Complex.exp (-((Real.pi : ℂ) * (starRingEnd ℂ) a * a / (2 * A)) * u ^ 2 - l * u)
def cst (a b τ A l : ℂ) : ℂ :=
  -((Real.pi : ℂ) * (starRingEnd ℂ) a * a / (2 * A)) * τ ^ 2 - l * τ +
    (Real.pi : ℂ) * b * (starRingEnd ℂ) b / (2 * A)
end PI.SSU


