-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ThetaNormCM
-- name    : Formalism_PeriodIntegrals_ThetaNormCM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:17.427524+00:00
-- url     : https://prove2.me/theorems/0f09692c-f601-427f-be38-3976bc0de9ff
-- title:
--   Theta Norm CM
-- statement:
--   Definitions and structural lemmas for Theta Norm CM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ThetaNormCM.lean

import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.ThetaNormCM
def hf1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (PI.area Λ : ℂ)
def al1 (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : ℂ := (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (hf1 Λ x x).re))
def IsTheta0 (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ (∀ x ∈ Λ, ∀ z, al1 d Λ x * PI.U1 Λ x G z = G z) ∧ G 0 = 1
def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (hf1 Λ z z).re)
def IsTwoTorsionPointUnkilled (d : ℕ) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt d : ℂ)) / 2) * t ∉ Λ
end PI.ThetaNormCM
namespace PI
open PI.ThetaNormCM in

def ThetaNormCM : Prop :=
  ∀ d : ℕ, Squarefree d → d % 8 = 7 →
    ∀ (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im →
    (∀ x ∈ AddSubgroup.closure ({ω₁, ω₁ * τ} : Set ℂ),
      ((1 + Complex.I * (Real.sqrt d : ℂ)) / 2) * x ∈ AddSubgroup.closure ({ω₁, ω₁ * τ} : Set ℂ)) →
    ∀ a b : ℕ, a ≤ 1 → b ≤ 1 →
    IsTwoTorsionPointUnkilled d (AddSubgroup.closure {ω₁, ω₁ * τ}) (ω₁ * ((1 - (a : ℂ)) * τ + (1 - (b : ℂ))) / 2) →
    ∀ G, IsTheta0 d (AddSubgroup.closure {ω₁, ω₁ * τ}) G →
      (normSq1 (AddSubgroup.closure {ω₁, ω₁ * τ}) G)⁻¹ = Real.sqrt (2 * τ.im) *
        (Real.exp (-Real.pi * (a : ℝ) ^ 2 * τ.im / 4) * ‖jacobiTheta₂ (((a : ℂ) * τ + (b : ℂ)) / 2) τ‖) ^ 2
end PI


