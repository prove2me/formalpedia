-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieFreePf
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LieFreePf
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:50:36.830318+00:00
-- url     : https://prove2.me/theorems/daf593b2-0688-4ed6-8811-767c7be69f44
-- title:
--   Lie Free Pf
-- statement:
--   Definitions and structural lemmas for Lie Free Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieFreePf.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieRel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tanBC_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj tvec_eig_iff isTan_tvec tcoord tcoord_spec univChartLoc tanBC_alg
  pushR pushR_left pushR_inj pushR_map tvec_tmap fB scaleD IsUnivChart dualMapA)
open Formalism.L2.Pj.LieRel Formalism.L2.Pj.LieAlg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
end Formalism.L2.Pj


