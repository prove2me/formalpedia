-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsRatioPoints
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsRatioPoints
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:30.423415+00:00
-- url     : https://prove2.me/theorems/ddc12360-638f-41eb-b9d8-b1cd53b0b5df
-- title:
--   Exists Ratio Points
-- statement:
--   Definitions and structural lemmas for Exists Ratio Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsRatioPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ESecStruct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TorusCoord
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
abbrev im {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) :
    (Over.map (thick R I e)).obj T ⟶ D.P.A :=
  (Over.map (thick R I e)).map x ≫ g.pG
abbrev cPt (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (χ : D.X) :
    (Over.map (thick R I e)).obj T ⟶ D.P.A :=
  DegPre.cT D ((Over.map (thick R I e)).obj T) χ
abbrev lhs {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T ⟶ thickObj R I e G)
    (χ : D.X) :=
  LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) (x * x').left)
    (DegPre.cubAtT D ((Over.map (thick R I e)).obj T) (cPt T χ) (im g x) (im g x'))
abbrev rhs {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x x' : T ⟶ thickObj R I e G)
    (χ : D.X) :=
  LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) x.left) (LB.pullGen D.P.L _ _ (g.t χ) x'.left)
def cubeVal {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X) (z : Z.left)
    (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι) (a b : Z ⟶ thickObj R I e G) :
    (Z.left.presheaf.stalk z)ˣ :=
  cubV D.cub (T := (Over.map (thick R I e)).obj Z) z J (cPt Z χ) (im g a) (im g b)
section Val
variable {T Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (χ : D.X) {z : Z.left}
  {J : (Z.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ
end Val
end GlobalTheory.TorusCoord


