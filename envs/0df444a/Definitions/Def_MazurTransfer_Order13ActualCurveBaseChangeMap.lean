-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualCurveBaseChangeMap
-- name    : MazurTransfer_Order13ActualCurveBaseChangeMap
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T03:31:47.237198+00:00
-- url     : https://prove2.me/theorems/4a0151ce-d6ba-4a44-a1fc-357409c82d6c
-- title:
--   The actual glued order-thirteen curve map under base change
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. The specified compatible chart morphisms glue to the actual curve morphism
--   $$f_{S/R}:C_S\longrightarrow C_R,\qquad f_{S/R}\circ\iota^S_i=\iota^R_i\circ\operatorname{Spec}(\phi_i),$$
--   where $i$ ranges over the ordinary and reciprocal charts, $\iota_i$ are their actual inclusions, and $\phi_i$ are the specified coordinate ring base-change maps.
--
--   The constructor uses the proved chart-map compatibility and the explicit gluing-morphism constructor. It retains both chart restriction identities, supplying the actual morphism in the Cartesian base-change square and the literal integral fibre dictionary.
-- source:
--   Three unchanged checked declarations from MazurTheorem Order13ActualCurveChangeOfBaseMorphism.lean: curveMap, ordinaryChartMap_curveMap and reciprocalChartMap_curveMap, selected by the Lean declaration and syntax oracles. Supporting chart compatibility is a separate Proved public theorem. All three complete original kernel types are verified by closed witnesses. Vas and contributors, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual change-of-base morphism of the literal glued
order-thirteen curve, built from the checked coordinate and overlap maps.
Named downstream consumer: constructing the isomorphism from its base change
to the literal curve over the new ring. No such isomorphism is assumed.
-/
import Definitions.Def_MazurTransfer_Order13GluedCurveMorphism
import Definitions.Def_MazurTransfer_Order13BaseChangeChartMorphisms
import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_chartMapToOriginal_compatible


noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
universe u
variable (K : Type u) [CommRing K]





variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]













def curveMap : curveScheme S ⟶ curveScheme R :=
  Order13GluedCurveMaps.desc S (chartMapToOriginal R S) (chartMapToOriginal_compatible R S)

@[reassoc]
theorem ordinaryChartMap_curveMap :
    ordinaryChartMap S ≫ curveMap R S =
      Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryChartMap R :=
  Order13GluedCurveMaps.chartMap_desc S (chartMapToOriginal R S)
    (chartMapToOriginal_compatible R S) Chart.ordinary

@[reassoc]
theorem reciprocalChartMap_curveMap :
    reciprocalChartMap S ≫ curveMap R S =
      Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalChartMap R :=
  Order13GluedCurveMaps.chartMap_desc S (chartMapToOriginal R S)
    (chartMapToOriginal_compatible R S) Chart.reciprocal

end MazurTransfer.Order13ActualCurveBaseChange






#print axioms MazurTransfer.Order13ActualCurveBaseChange.curveMap
#print axioms MazurTransfer.Order13ActualCurveBaseChange.ordinaryChartMap_curveMap
#print axioms MazurTransfer.Order13ActualCurveBaseChange.reciprocalChartMap_curveMap


