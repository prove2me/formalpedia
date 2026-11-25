-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassZero
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_GreenMassZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:58.039799+00:00
-- url     : https://prove2.me/theorems/25cebe3c-25d6-4d76-9f8f-1fe48b9bd18d
-- title:
--   Green Mass Zero
-- statement:
--   Definitions and structural lemmas for Green Mass Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/GreenMassZero.lean

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
def GreenMassZero.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ t, S.J 0 ε t ≤ η
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


