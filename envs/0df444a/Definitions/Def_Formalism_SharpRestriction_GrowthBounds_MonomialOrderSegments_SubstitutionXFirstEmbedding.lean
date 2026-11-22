-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:22.534819+00:00
-- url     : https://prove2.me/theorems/4ebbb20c-6659-4f72-b856-8c8589ff2c89
-- title:
--   Substitution XFirst Embedding
-- statement:
--   Definitions and structural lemmas for Substitution XFirst Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
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
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
end TwistData
end Formalism.MainNotions.PlaneGram


