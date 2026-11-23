-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:28.938668+00:00
-- url     : https://prove2.me/theorems/9e29e2f1-4b2e-4e75-9915-cdb23055b88c
-- title:
--   Cancel Sec Act
-- statement:
--   Definitions and structural lemmas for Cancel Sec Act, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/CancelSecAct.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WchartPullLe
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
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.WeightPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
abbrev Te (D : DegPre R) (I : Ideal R) (e : ℕ) := splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X
def act : Te D I e ⊗ thickObj R I e G ⟶ thickObj R I e G :=
  lift (fst (Te D I e) (thickObj R I e G) ≫ g.i) (snd _ _) ≫ μ[thickObj R I e G]
def sec : thickObj R I e G ⟶ Te D I e ⊗ thickObj R I e G :=
  lift (toUnit _ ≫ η[Te D I e]) (𝟙 _)
end ReciprocityTheory.ChartRestriction.G.Out.WeightPf


