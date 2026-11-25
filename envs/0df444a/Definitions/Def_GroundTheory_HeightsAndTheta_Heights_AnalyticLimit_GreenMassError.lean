-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassError
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassError
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:30:43.495891+00:00
-- url     : https://prove2.me/theorems/6322a5b4-2707-4a5f-a7c9-6736fb20c386
-- title:
--   Green Mass Error
-- statement:
--   Definitions and structural lemmas for Green Mass Error, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/GreenMassError.lean

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
def GreenMassError.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1), ∀ δ, 0 < δ → ∃ τ, 0 < τ ∧ ∀ t₀ t, 0 < t → t ≤ t₀ → t₀ ≤ τ →
      S.ell₀ ≤ ell t₀ → S.errW a ha t₀ t ≤ δ ∧ S.errDiv a ha t₀ t ≤ δ
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


