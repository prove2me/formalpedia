-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardChoiceLe
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardChoiceLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:16.141801+00:00
-- url     : https://prove2.me/theorems/94e0fb50-8936-491a-a25b-b9d21a1ed936
-- title:
--   Card Choice Le
-- statement:
--   Definitions and structural lemmas for Card Choice Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/CardChoiceLe.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IteratedDerivListBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_OneAddPowSubOneLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}
section Count
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)
end Count
section Data
variable [IsCMField E] (X : PT E) (bs : Fin nb → Block E n X.dim)
end Data
end
end ReciprocityTheory.ChartRestriction.G.I2


