-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverPoly
-- name    : Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverPoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:34.389014+00:00
-- url     : https://prove2.me/theorems/f7a7ebb1-bcf3-4219-af68-ef1e4ce81367
-- title:
--   Cover Poly
-- statement:
--   Definitions and structural lemmas for Cover Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverPoly.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.NCov
open Module
variable {K₁ K₂ V₁ V₂ : Type*} [Field K₁] [Field K₂] [AddCommGroup V₁] [Module K₁ V₁] [AddCommGroup V₂]
  [Module K₂ V₂]
end Formalism.L2.NCov


