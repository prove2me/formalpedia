-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHBSt
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHBSt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:30:07.664205+00:00
-- url     : https://prove2.me/theorems/20f9e411-07a7-5812-85e4-711c04427ddc
-- title:
--   PNTDHBSt
-- statement:
--   Definitions and structural lemmas for PNTDHBSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHBSt.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
def DeuringHeilbronnMB : Prop :=
  ∃ (c₀ c₁ c₂ : ℝ) (B : ℕ), 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → β₁ < 1 →
    IsLZero χ ρ → 1 - c₀ ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ B)) / Real.log ((M : ℝ) * T) ≤ 1 - ρ.re
def ZeroSumOfB : Prop := LogDensityM → DeuringHeilbronnMB → ZeroSum
end Formalism.HermitianLattices.Ext.PrimesInProgressions


