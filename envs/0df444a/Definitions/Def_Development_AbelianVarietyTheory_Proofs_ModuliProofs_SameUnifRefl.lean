-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:45.645847+00:00
-- url     : https://prove2.me/theorems/7272ce7f-0fb2-45d9-879d-fca3ff3030ef
-- title:
--   Same Unif Refl
-- statement:
--   Definitions and structural lemmas for Same Unif Refl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SameUnifRefl.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
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
namespace GlobalTheory.TorsionFormCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
def RigAlong {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (ε : G' ⟶ G) (L : RigLB G) (L' : RigLB G') (w : LB.Iso L'.L (L.L.pull ε.left)) : Prop :=
  w.IsGen ∧ PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (𝟙 _)
variable {R : Type} [CommRing R] [IsDomain R]
def SameUnif {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G' G : Over (Sp R)}
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (ε : G' ≅ G)
    (U : UnifPre I D A G) (U' : UnifPre I D A G') : Prop :=
  U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom ∧
    ∃ w : LB.Iso U'.LG.L (U.LG.L.pull ε.hom.left), RigAlong ε.hom U.LG U'.LG w ∧ ∀ e : ℕ,
      (U'.gt e).q = (Over.pullback (thick R I e)).map ε.hom ≫ (U.gt e).q ∧
      (∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ ((U'.gt e).t χ)
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (thick R I e)).map ε.hom).left)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
        (jL' : U'.LG.L.ι), (U'.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM →
        ε.hom.left ((fstG I e G').left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
        gw (U'.w e) r z jM (fun _ => jL') =
          gw (U.w e) (r ≫ ((Over.pullback (thick R I e)).map ε.hom).left) z jM (fun _ => jL) *
            gw w (r ≫ (fstG I e G').left) z jL jL'
def IsIdPull {D : DegPre R} (hD : IsPullDeg (RingHom.id R) D D) : Prop :=
  (∀ x, hD.xe x = x) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ ∧
    ∀ (Y : Scheme.{0}) (f : Y ⟶ D.P.A.left) (y : Y) (j k : D.P.L.ι), f y ∈ D.P.L.U j → f y ∈ D.P.L.U k →
      gw hD.w f y j k = gm f y _ (D.P.L.g j k)
end GlobalTheory.TorsionFormCompare


