-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_LiRenameMon
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_LiRenameMon
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:05.135993+00:00
-- url     : https://prove2.me/theorems/806621cd-97a6-4005-b5e4-066af37e4805
-- title:
--   Li Rename Mon
-- statement:
--   Definitions and structural lemmas for Li Rename Mon, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialFactorials/LiRenameMon.lean

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_SSD_kap_add
import Theorems.Thm_Formalism_GM_M_SSD_kap_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.G.SymmetricFormBlocks
open MvPolynomial Finset Formalism.GM.M.SSD
section LI
variable {σ τ K : Type} [Field K] [DecidableEq σ] (e : τ → σ) (he : Function.Injective e)
def decode (M : Finset (σ →₀ ℕ)) : MvPolynomial σ K →ₗ[K] (M → MvPolynomial τ K) where
  toFun Q := fun β => kap _ (F_inj e he 0 (β : σ →₀ ℕ)) Q
  map_add' Q Q' := by funext β; exact kap_add _ _ Q Q'
  map_smul' c Q := by funext β; exact kap_smul _ _ c Q
end LI
end Formalism.MainNotions.G.SymmetricFormBlocks
end


