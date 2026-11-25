-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassStep
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassStep
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:24.871504+00:00
-- url     : https://prove2.me/theorems/cf464897-0259-5224-8d0a-27daff1df69f
-- title:
--   Green Mass Step
-- statement:
--   Definitions and structural lemmas for Green Mass Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/GreenMassStep.lean

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
def GreenMassStep.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W)
    (a : ℕ) (ha : a < D + 1) (ε t : ℝ), 0 < ε → 0 < t → S.ell₀ ≤ ell t →
      S.J (a + 1) ε t ≤ S.J a ε t + S.plTerm a ha ε t
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


