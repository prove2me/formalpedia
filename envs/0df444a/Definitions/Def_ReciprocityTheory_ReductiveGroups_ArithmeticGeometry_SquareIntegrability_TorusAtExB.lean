-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtExB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtExB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:38:35.197409+00:00
-- url     : https://prove2.me/theorems/82e68fd5-ce43-4737-bb9e-6dd6c1c1ccb0
-- title:
--   Torus At Ex B
-- statement:
--   Definitions and structural lemmas for Torus At Ex B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtExB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
noncomputable section
namespace TX
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def Ef (u v : Fin r → E) : ℚ := Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v)
end TX
end
end ReciprocityTheory.ChartRestriction.G.I2


