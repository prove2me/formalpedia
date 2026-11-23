-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:13.140448+00:00
-- url     : https://prove2.me/theorems/c80f512b-20db-4981-9b8c-9319f72ea1d7
-- title:
--   Is Mon Hom Of Mul
-- statement:
--   Definitions and structural lemmas for Is Mon Hom Of Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsMonHomOfMul.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_of_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
section Transport
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
def pw (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι) :
    (Z.presheaf.stalk z)ˣ := ∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k
end Transport
section Pull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
theorem pull_grp (hD : IsPullDeg φ D D') :
    IsGrpPullback D'.P.A D.P.A (spMap φ) (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  have := hD.e_hom
  exact ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback D.P.A (specOf φ))).congr (Category.id_comp _) rfl
def vS {F : Type} [Field F] {X : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {ψ : K → (Sp F ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb M ψ ε)) (y : Sp F) (J : (Sp F ⟶ X) → M.ι) : ((Sp F).presheaf.stalk y)ˣ := val t (𝟙 _) y J
def thS (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F] (y : Sp F) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι)
    (a b c : TF (R := R) F ⟶ D.P.A) : ((Sp F).presheaf.stalk y)ˣ := th D (T := TF (R := R) F) y J a b c
def vK {F : Type} [Field F] [Algebra (FractionRing R) F] {X : Scheme.{0}} {M : LB X} {K : Type} [Fintype K]
    {ψ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M ψ ε)) (y : Sp F) (J : (Sp F ⟶ X) → M.ι) :
    ((Sp F).presheaf.stalk y)ˣ := val t (𝟙 _ ≫ jFK (R := R) F) y J
end Pull
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


