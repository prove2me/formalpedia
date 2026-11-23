-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:25.588041+00:00
-- url     : https://prove2.me/theorems/185c062d-2388-4e1d-9c04-321b79650ff9
-- title:
--   Is Universal Chart Of Formal Group Chart
-- statement:
--   Definitions and structural lemmas for Is Universal Chart Of Formal Group Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChartUniv
section Jets
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
def jetRen {κ κ' : Type} (f : κ → κ') (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ' m :=
  jetLift R (RingHom.ker (jetAug R κ' m)) (ker_jetAug_pow κ' m) (fun j => zR m (f j)) (fun j => zR_mem_ker m (f j))
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
end Jets
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
end GlobalTheory.ChartUniv


