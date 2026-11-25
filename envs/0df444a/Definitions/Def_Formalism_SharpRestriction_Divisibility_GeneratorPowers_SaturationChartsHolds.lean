-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:57.651796+00:00
-- url     : https://prove2.me/theorems/2820fa17-fec5-4329-a6be-8459f8fc5891
-- title:
--   Saturation Charts Holds
-- statement:
--   Definitions and structural lemmas for Saturation Charts Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/SaturationChartsHolds.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExistsBasisOfSaturated
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
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
namespace Formalism.L2.Pj.SaturatedCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
section Gen
variable {S : Scheme.{0}} {M : Over S} [MonObj M]
end Gen
section Tan
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
variable (t : SAB H (Sp V))
def toT (v : Sp (DualNumber V) ⟶ t.G.left) (h : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) ⟶ t.G :=
  Over.homMk v h
def eT : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) ⟶ tEpsG (𝟙 (Sp V)) :=
  Over.homMk (𝟙 _) (by simp)
def eT' : tEpsG (𝟙 (Sp V)) ⟶ ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := V) (DualNumber V) :=
  Over.homMk (𝟙 _) (by simp)
end Tan
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
end Main
end Formalism.L2.Pj.SaturatedCharts


