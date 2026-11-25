-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsSplitIdempotentOfSplitAt
-- name    : Development_AutomorphicArithmetic_CMTraceForms_ExistsSplitIdempotentOfSplitAt
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:00.707549+00:00
-- url     : https://prove2.me/theorems/a0d7df24-163d-4369-93d6-e2e29f99286a
-- title:
--   Exists Split Idempotent Of Split At
-- statement:
--   Definitions and structural lemmas for Exists Split Idempotent Of Split At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/ExistsSplitIdempotentOfSplitAt.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
namespace UpperTheory.Depth.SplitIdem
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end UpperTheory.Depth.SplitIdem


