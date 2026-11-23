-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:55.695877+00:00
-- url     : https://prove2.me/theorems/01e48b10-57ed-43ae-8697-4c7ad083ce14
-- title:
--   Mass Ratio Bound
-- statement:
--   Definitions and structural lemmas for Mass Ratio Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
def zetaGL3GL2 : ℝ := ∑' m : ℕ, 1 / (m : ℝ) ^ ((3 : ℝ) / 2)
end Formalism.MainNotions.MassRatioZetaBound
end


