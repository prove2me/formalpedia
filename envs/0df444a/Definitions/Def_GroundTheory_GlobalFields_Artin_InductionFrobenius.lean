-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_InductionFrobenius
-- name    : GroundTheory_GlobalFields_Artin_InductionFrobenius
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:48.911309+00:00
-- url     : https://prove2.me/theorems/24e3ff65-7860-5f2a-ad35-1a428d37fff1
-- title:
--   Induction Frobenius
-- statement:
--   Definitions and structural lemmas for Induction Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InductionFrobenius.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open NumberField IsDedekindDomain
open scoped Pointwise
namespace GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
end GroundTheory.Global.Artin


