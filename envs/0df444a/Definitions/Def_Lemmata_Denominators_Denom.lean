-- Prove2me | Definitions.Def_Lemmata_Denominators_Denom
-- name    : Lemmata_Denominators_Denom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:32.440902+00:00
-- url     : https://prove2.me/theorems/849b4919-cba6-4ea7-829a-adb084219131
-- title:
--   Denom
-- statement:
--   Definitions and structural lemmas for Denom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/Denominators/Denom.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace Bl.DenominatorsAlt
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
end Bl.DenominatorsAlt


