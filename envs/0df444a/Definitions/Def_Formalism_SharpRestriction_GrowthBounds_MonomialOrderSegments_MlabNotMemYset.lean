-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MlabNotMemYset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:52.777875+00:00
-- url     : https://prove2.me/theorems/f468792a-e90d-4905-bcce-0722967e6a4e
-- title:
--   Mlab Not Mem Yset
-- statement:
--   Definitions and structural lemmas for Mlab Not Mem Yset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MlabNotMemYset.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_support_dg_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
section
variable {K : Type} [Field K]
end
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K)
theorem Good.dg {p : ℕ} {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) (f : D.EM → K) :
    D.Good p (Formalism.MainNotions.PlaneGram.dg f Z) := fun ζ hζ => hZ ζ (support_dg_subset f Z hζ)
end TwistData
section Main
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
end Main
end Formalism.MainNotions.PlaneGram


