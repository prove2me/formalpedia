-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:07.824037+00:00
-- url     : https://prove2.me/theorems/04c22013-1b04-4de7-82ec-9e653849add1
-- title:
--   Right Half With
-- statement:
--   Definitions and structural lemmas for Right Half With, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZeroWindow/RightHalfWith.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindow
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric
namespace PI.ZW
def RightNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}
def RightHalfWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), (χ ≠ 1 ∨ N = 1) → ∀ t : ℝ,
    (RightNear χ t).Finite ∧
    ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))
def RightChiWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ t : ℝ,
    (RightNear χ t).Finite ∧
    ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))
def RightOneWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), N = 1 → ∀ t : ℝ,
    (RightNear χ t).Finite ∧
    ∑ᶠ ρ ∈ RightNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))
def RightChi : Prop := PI.LBoundRight → PI.LInvRight → ∃ C : ℝ, RightChiWith C
def RightOne : Prop := PI.ZetaBoundRight → PI.LInvRight → ∃ C : ℝ, RightOneWith C
def Transfer : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
    DirichletCharacter.LFunction χ ρ = 0 →
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 ∧
    analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≤
      analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ)
def JensenCount : Prop :=
  ∀ (f : ℂ → ℂ) (c : ℂ) (M : ℝ), AnalyticOnNhd ℂ f (closedBall c (19 / 10)) → f c ≠ 0 → 1 ≤ M →
    (∀ z ∈ sphere c (19 / 10), ‖f z‖ ≤ M) →
    ∀ S : Set ℂ, S ⊆ {z | z ∈ closedBall c (37 / 20) ∧ f z = 0} →
      S.Finite ∧
      ∑ᶠ z ∈ S, (analyticOrderNatAt f z : ℝ) ≤ Real.log (M / ‖f c‖) / Real.log ((19 / 10) / (37 / 20))
end PI.ZW


