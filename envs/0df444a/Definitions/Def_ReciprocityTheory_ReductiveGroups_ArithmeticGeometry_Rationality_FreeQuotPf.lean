-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:51.064619+00:00
-- url     : https://prove2.me/theorems/3c5887da-6f15-4ab1-8253-9aa0a69443c7
-- title:
--   Free Quot Pf
-- statement:
--   Definitions and structural lemmas for Free Quot Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FreeQuotPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Lemmata_MiscLemmasJ_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Module
section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
end
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


