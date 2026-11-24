-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_CrossFix
-- name    : ReciprocityTheory_Chebotarev_CrossFix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:59.081411+00:00
-- url     : https://prove2.me/theorems/b221d11a-6579-46a2-82a1-8bc653c09dfb
-- title:
--   Cross Fix
-- statement:
--   Definitions and structural lemmas for Cross Fix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CrossFix.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
namespace ReciprocityTheory.Cheb
variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]
end ReciprocityTheory.Cheb


