-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_PFlagWeightLevi
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T12:40:22.892928+00:00
-- url     : https://prove2.me/theorems/ea056eee-b2d1-466c-a314-323e9b2701da
-- title:
--   PFlag Weight Levi
-- statement:
--   Definitions and structural lemmas for PFlag Weight Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PFlagWeightLevi.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm
noncomputable section
def flagTerm (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N)
    (z : (Σ _ : Fin f, LowerPair N) → ℂ) : ℝ :=
  if h : j.2.val + 1 < N then
    (lam j.1 j.2 - lam j.1 ⟨j.2.val + 1, h⟩) * flagPs N p (j.2.val + 1) h.le fun q => z ⟨j.1, q⟩
  else 0
end
end GroundTheory.Heights₂.Heights.FourB


