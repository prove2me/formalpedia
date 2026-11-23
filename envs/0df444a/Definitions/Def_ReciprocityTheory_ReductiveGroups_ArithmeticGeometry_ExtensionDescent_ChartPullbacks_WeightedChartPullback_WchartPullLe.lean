-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:38.924737+00:00
-- url     : https://prove2.me/theorems/a4eeddb2-c9a5-43c9-984f-f983d71d38a5
-- title:
--   Wchart Pull Le
-- statement:
--   Definitions and structural lemmas for Wchart Pull Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/WchartPullLe.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Semi.LBVal
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
lemma wchart_pull_le (φ : K → (Y ⟶ X)) (h : Z ⟶ Y) (j : K → L.ι) :
    LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
end ReciprocityTheory.ChartRestriction.G.Semi.LBVal
namespace ReciprocityTheory.ChartRestriction.G.Out.LBVal
open Semi
end ReciprocityTheory.ChartRestriction.G.Out.LBVal


