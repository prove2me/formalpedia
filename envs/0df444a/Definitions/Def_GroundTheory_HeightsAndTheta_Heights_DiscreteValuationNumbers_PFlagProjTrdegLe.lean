-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagProjTrdegLe
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagProjTrdegLe
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:36:27.1108+00:00
-- url     : https://prove2.me/theorems/fab7e0ff-3bf5-4683-9e0d-8e9b887f2c04
-- title:
--   PFlag Proj Trdeg Le
-- statement:
--   Definitions and structural lemmas for PFlag Proj Trdeg Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagProjTrdegLe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PAdjoinTrdegAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace FlagProjTrdegLe
def zeroNewBlocks {O K : Type} [CommRing O] {ι : K → Type} {M M' : ℕ} :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → MRing ι O
  | ⟨some (some k), i⟩ => X ⟨k, i⟩
  | ⟨some none, _⟩ => 0
  | ⟨none, _⟩ => 0
end FlagProjTrdegLe
end
end GroundTheory.Heights₂.Heights.NumbersDVR


