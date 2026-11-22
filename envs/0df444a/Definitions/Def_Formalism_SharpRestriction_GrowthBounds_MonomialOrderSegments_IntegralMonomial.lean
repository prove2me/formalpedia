-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:30.644946+00:00
-- url     : https://prove2.me/theorems/8e0a2f49-4072-4d72-86ec-626d30a6575a
-- title:
--   Integral Monomial
-- statement:
--   Definitions and structural lemmas for Integral Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/IntegralMonomial.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsMonomialOrder
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
section General
variable {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)} {σ : Type}
end General
section Deg
variable {K : Type} [Field K] {L L' : Type} {r : ℕ}
end Deg
end Formalism.MainNotions.PlaneGram


