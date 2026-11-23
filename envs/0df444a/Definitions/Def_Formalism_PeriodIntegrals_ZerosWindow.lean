-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ZerosWindow
-- name    : Formalism_PeriodIntegrals_ZerosWindow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:00.262066+00:00
-- url     : https://prove2.me/theorems/98e6191f-e143-453a-80ac-719dbd27fa33
-- title:
--   Zeros Window
-- statement:
--   Definitions and structural lemmas for Zeros Window, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ZerosWindow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
def ZerosNear {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ DirichletCharacter.LFunction χ ρ = 0}
def ZerosWindowWith (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    (ZerosNear χ t).Finite ∧
    ∑ᶠ ρ ∈ ZerosNear χ t, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      C * Real.log (N * (|t| + 2))
def ZerosWindow : Prop := ∃ C : ℝ, 0 < C ∧ ZerosWindowWith C
end PI


