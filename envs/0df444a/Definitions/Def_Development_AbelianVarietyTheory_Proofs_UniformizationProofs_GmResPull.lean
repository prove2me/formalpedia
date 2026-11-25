-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmResPull
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmResPull
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:37:46.937608+00:00
-- url     : https://prove2.me/theorems/130d587b-cfb9-5927-8bf0-84838cd4dc8c
-- title:
--   Gm Res Pull
-- statement:
--   Definitions and structural lemmas for Gm Res Pull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmResPull.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Theorems.Thm_GlobalTheory_UU_toBase_mul_pullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ToChart
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)
def fstHom (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
    toBase_mul_pullback G (thick R I e) T x y
variable {I e} {D : DegPre R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def projHom (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ g.pG) fun x y => by
    have := g.q_hom
    have h : ∀ a : T ⟶ thickObj R I e G, (Over.map (thick R I e)).map a ≫ g.pG = fstHom I e D.P.A T (a ≫ g.q) :=
      fun a => by rw [← Category.assoc, ← Functor.map_comp]; rfl
    rw [h, h, h, MonObj.mul_comp, map_mul]
variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G)
end GlobalTheory.UU.ToChart
end


