-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_LinearRestriction_ResPullUVal
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_LinearRestriction_ResPullUVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:13.264706+00:00
-- url     : https://prove2.me/theorems/ecf8bd0d-001d-4816-a5f8-31865d83138c
-- title:
--   Res Pull UVal
-- statement:
--   Definitions and structural lemmas for Res Pull UVal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/LinearRestriction/ResPullUVal.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.OLinPf
open ReciprocityTheory.ChartRestriction.G.Out Semi
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
namespace ILin
section Base
variable {I : Ideal R} {I' : Ideal R'} (φ : R →+* R')
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  (bc : G' ≅ (Over.pullback (specOf φ)).obj G)
end Base
end ILin
section ILin
variable {I : Ideal R} {I' : Ideal R'} (φ : R →+* R') {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : Unif I D A G}
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  {bc : G' ≅ (Over.pullback (specOf φ)).obj G}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))} {D' : DegData R' I'}
  {hD : IsPullDeg φ D.toPre D'.toPre} {U' : Unif I' D' A' G'}
  {O : Type} [CommRing O] [StarRing O]
namespace ILin
section Val
open Geo.Tor
end Val
end ILin
end ILin
end ReciprocityTheory.ChartRestriction.G.Out.OLinPf


