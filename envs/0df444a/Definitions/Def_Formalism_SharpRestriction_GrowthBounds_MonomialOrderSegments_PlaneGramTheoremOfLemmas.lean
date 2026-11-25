-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PlaneGramTheoremOfLemmas
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PlaneGramTheoremOfLemmas
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:37:27.161266+00:00
-- url     : https://prove2.me/theorems/dbdc52a6-c6d6-4a22-8bf1-71521555ee90
-- title:
--   Plane Gram Theorem Of Lemmas
-- statement:
--   Definitions and structural lemmas for Plane Gram Theorem Of Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/PlaneGramTheoremOfLemmas.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_RenamePullLCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_PrimedEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_OmegaValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
end Formalism.MainNotions.PlaneGram


