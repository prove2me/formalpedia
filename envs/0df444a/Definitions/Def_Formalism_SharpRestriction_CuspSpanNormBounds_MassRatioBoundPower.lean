-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBoundPower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:31.860715+00:00
-- url     : https://prove2.me/theorems/90083c47-fe25-4453-8f0d-9c21280cc61a
-- title:
--   Mass Ratio Bound Power
-- statement:
--   Definitions and structural lemmas for Mass Ratio Bound Power, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBoundPower.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.MassRatioBoundPower
open NumberField Formalism.MainNotions.MassRatioZetaBound
variable {K : Type*} [Field K] [NumberField K]
def cZ : ℕ := Nat.ceil (4 * zetaGL3GL2 / Real.log 2)
end Formalism.MainNotions.MassRatioBoundPower
end


