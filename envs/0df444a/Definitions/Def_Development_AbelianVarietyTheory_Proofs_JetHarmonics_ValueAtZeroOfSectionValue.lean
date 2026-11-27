-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ValueAtZeroOfSectionValue
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ValueAtZeroOfSectionValue
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-27T06:31:34.65016+00:00
-- url     : https://prove2.me/theorems/2b147010-05c7-4755-b8ce-cbe0804d84d5
-- title:
--   Value At Zero Of Section Value
-- statement:
--   Definitions and structural lemmas for Value At Zero Of Section Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ValueAtZeroOfSectionValue.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_VRatioGtStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetLemmaStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_IsUnivChart
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PhiValue
open ReciprocityTheory.ChartRestriction.G.DVR.TWM ReciprocityTheory.ChartRestriction.G.DVR.TWO ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation ReciprocityTheory.ChartRestriction.G.DVR.QForm ReciprocityTheory.ChartRestriction.G.DVR.PeriodicValuation
section Integral
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) {X : Scheme.{0}} {L : LB X}
end Integral
end GlobalTheory.PhiValue


