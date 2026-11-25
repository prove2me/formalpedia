-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DegreeInfimum_PlaceDegreeSums
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DegreeInfimum_PlaceDegreeSums
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:12:11.331807+00:00
-- url     : https://prove2.me/theorems/b77597fb-460a-4fb0-9139-9e65d69288d4
-- title:
--   Place Degree Sums
-- statement:
--   Definitions and structural lemmas for Place Degree Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DegreeInfimum/PlaceDegreeSums.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.QAt.PlaceDegreeSums
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
end Formalism.L2.Pj.QAt.PlaceDegreeSums


