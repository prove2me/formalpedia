-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__PageThm_f2e9c9300440fc89
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__PageThm_f2e9c9300440fc89
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:14.061774+00:00
-- url     : https://prove2.me/theorems/dff3fd6a-5925-4dcd-bfa3-d445b2194be0
-- title:
--   Page Thm
-- statement:
--   Definitions and structural lemmas for Page Thm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/PageThm.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.An
def PageThm : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (β₁ β₂ : ℝ),
    χ₁.IsPrimitive → χ₂.IsPrimitive → χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → (q₁ : ℝ) ≤ Q → (q₂ : ℝ) ≤ Q →
    1 - c / Real.log Q < β₁ → β₁ < 1 → 1 - c / Real.log Q < β₂ → β₂ < 1 →
    DirichletCharacter.LFunction χ₁ β₁ = 0 → DirichletCharacter.LFunction χ₂ β₂ = 0 →
    q₁ = q₂ ∧ ∀ n : ℕ, χ₁ (n : ZMod q₁) = χ₂ (n : ZMod q₂)
end GlobalTheory.Mem.An


