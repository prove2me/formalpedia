-- Prove2me | Definitions.Def_MazurTransfer_Order13BaseChangeChartMorphisms
-- name    : MazurTransfer_Order13BaseChangeChartMorphisms
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T03:17:06.120005+00:00
-- url     : https://prove2.me/theorems/720e2f88-2319-41b8-87fd-fe14517533e4
-- title:
--   Actual base-change isomorphisms and morphisms for the two affine charts
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. The concrete quadratic coordinate-algebra equivalences give scheme isomorphisms for both actual affine charts,
--   $$\operatorname{Spec}S\times_{\operatorname{Spec}R}C_{R,i}\;\cong\;C_{S,i},$$
--   where $i$ is the ordinary or reciprocal chart. The same actual coordinate ring maps define morphisms $\delta_i:C_{S,i}\to C_R$ by composition with the chart inclusions.
--
--   This constructor interface keeps overlap compatibility as a separate theorem. It supplies the chart morphism family for the actual whole-curve map and the affine isomorphisms used to prove its chart preimage squares are Cartesian.
-- source:
--   Three unchanged checked constructor bodies selected by the Lean declaration and syntax oracles: ordinaryChartIso and reciprocalChartIso from Order13AffineChartBaseChangeSchemeIsomorphisms.lean, and chartMapToOriginal from Order13ActualCurveChangeOfBaseMorphism.lean. Other proof declarations are omitted; the three complete original public types are verified by closed kernel witnesses. Vas and contributors, Apache-2.0.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual affine chart base-change isomorphisms and
chart maps to the original curve, with compatibility kept as a separate
proof obligation. Named downstream consumers: the chart-map compatibility
proof and the actual chart preimage Cartesian squares. -/
import Definitions.Def_MazurTransfer_Order13CoordinateBaseChangeMaps
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual scheme isomorphisms from the base-changed ordinary
and reciprocal charts to the literal charts over the new base ring.
Named downstream consumer: gluing these affine fibre identifications along
the checked reciprocal transition to identify the actual entire curve family.
-/


noncomputable section
namespace MazurTransfer.Order13ChartSchemeBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def ordinaryChartIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (ordinaryChartToBase R) ≅ MazurTorsion.XOneThirteenAffineCurve.scheme S :=
  (pullbackSpecIso R S (CoordinateRing R)).trans
    (Scheme.Spec.mapIso
      (Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv R S).symm.toRingEquiv.toCommRingCatIso.op)

def reciprocalChartIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (reciprocalChartToBase R) ≅ reciprocalScheme S :=
  (pullbackSpecIso R S (ReciprocalRing R)).trans
    (Scheme.Spec.mapIso
      (Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv R S).symm.toRingEquiv.toCommRingCatIso.op)









end MazurTransfer.Order13ChartSchemeBaseChange








end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual change-of-base morphism of the literal glued
order-thirteen curve, built from the checked coordinate and overlap maps.
Named downstream consumer: constructing the isomorphism from its base change
to the literal curve over the new ring. No such isomorphism is assumed.
-/


noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
universe u
variable (K : Type u) [CommRing K]





variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]









def chartMapToOriginal : ∀ i : Chart.{u}, chartScheme S i ⟶ curveScheme R
  | .ordinary => Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryChartMap R
  | .reciprocal => Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalChartMap R









end MazurTransfer.Order13ActualCurveBaseChange






end

#print axioms MazurTransfer.Order13ChartSchemeBaseChange.ordinaryChartIso
#print axioms MazurTransfer.Order13ChartSchemeBaseChange.reciprocalChartIso
#print axioms MazurTransfer.Order13ActualCurveBaseChange.chartMapToOriginal


