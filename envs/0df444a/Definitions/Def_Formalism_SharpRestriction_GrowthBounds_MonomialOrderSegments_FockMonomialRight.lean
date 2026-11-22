-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:39:40.289665+00:00
-- url     : https://prove2.me/theorems/6c5241a8-6b6c-400e-8fb6-7a4ec0a529a3
-- title:
--   Fock Monomial Right
-- statement:
--   Definitions and structural lemmas for Fock Monomial Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
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
variable {K : Type} [Field K]
section Elem
variable (v : AddValuation K (WithTop ℚ))
end Elem
section Fock
variable {σ : Type}
end Fock
section BB
variable (v : AddValuation K (WithTop ℚ)) {σ : Type}
end BB
end Formalism.MainNotions.PlaneGram


