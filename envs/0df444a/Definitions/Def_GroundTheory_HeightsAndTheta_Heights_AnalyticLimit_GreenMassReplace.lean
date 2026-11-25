-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassReplace
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassReplace
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:51.070748+00:00
-- url     : https://prove2.me/theorems/5137d4be-0d94-485b-a503-bf39bc3c661a
-- title:
--   Green Mass Replace
-- statement:
--   Definitions and structural lemmas for Green Mass Replace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/GreenMassReplace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_UIObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)
noncomputable section
def GreenMassReplace.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∃ Cκ, 0 ≤ Cκ ∧ ∀ (a : ℕ) (ha : a < D + 1) (t₀ : ℝ), 0 < t₀ → S.ell₀ ≤ ell t₀ →
      ∃ K, 0 ≤ K ∧ ∀ ε t, 0 < ε → ε ≤ 1 → 0 < t → t ≤ t₀ →
        S.plTerm a ha ε t ≤ K * S.J a ε t + Cκ * S.errW a ha t₀ t + 2 * S.errDiv a ha t₀ t
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


