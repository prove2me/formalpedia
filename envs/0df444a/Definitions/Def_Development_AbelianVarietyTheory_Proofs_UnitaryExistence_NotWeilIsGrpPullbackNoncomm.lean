-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NotWeilIsGrpPullbackNoncomm
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:31.128423+00:00
-- url     : https://prove2.me/theorems/ace09cbe-4936-52f6-9ec2-3cc61af4cd0f
-- title:
--   Not Weil Is Grp Pullback Noncomm
-- statement:
--   Definitions and structural lemmas for Not Weil Is Grp Pullback Noncomm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NotWeilIsGrpPullbackNoncomm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
namespace WeilNoncomm
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
def oneChart (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
def sgn (R : Type) [CommRing R] (b : Bool) : Rˣ := cond b (-1) 1
def twoCharts (X : Scheme.{0}) : LB X := ⟨Bool, fun _ => ⊤, fun i j => sgn _ (xor i j)⟩
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
def loc {L : LB G.left} {k : ℤ} {T : Over S} (z : T.left) (θ : ThetaGrp G L k T) (a : T ⟶ G) (i j : L.ι) :
    (T.left.presheaf.stalk z)ˣ :=
  gm (lift (𝟙 T) a).left z (LB.wchart L ![(snd T G).left, (translPt G θ.pt).left] ![i, j]) (θ.φ.s ![i, j])
@[ext] structure Heis (R : Type) where

  a : R

  b : R

  c : R
namespace Heis
variable {R R' : Type} [CommRing R] [CommRing R']
instance : Mul (Heis R) := ⟨fun g h => ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩⟩
instance : One (Heis R) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (Heis R) := ⟨fun g => ⟨-g.a, -g.b, -g.c + g.a * g.b⟩⟩
theorem mul_def (g h : Heis R) : g * h = ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩ := rfl
theorem one_def : (1 : Heis R) = ⟨0, 0, 0⟩ := rfl
theorem inv_def (g : Heis R) : g⁻¹ = ⟨-g.a, -g.b, -g.c + g.a * g.b⟩ := rfl
instance : Group (Heis R) := Group.ofLeftAxioms
  (fun g h k => by ext <;> simp only [mul_def] <;> ring)
  (fun g => by ext <;> simp [mul_def, one_def])
  (fun g => by ext <;> simp [mul_def, one_def, inv_def])
def map (f : R →+* R') : Heis R →* Heis R' :=
  MonoidHom.mk' (fun g => ⟨f g.a, f g.b, f g.c⟩) fun g h => by ext <;> simp [mul_def]
end Heis
def heisFunctor (S : Scheme.{0}) : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Heis Γ(T.unop.left, ⊤))
  map f := GrpCat.ofHom (Heis.map f.unop.left.appTop.hom)
  map_id T := by
    ext g <;> simp [Heis.map]
  map_comp f g := rfl
abbrev heisScheme (S : Scheme.{0}) : Over S := Over.mk (𝔸(Fin 3; S) ↘ S)
def heisRepr (S : Scheme.{0}) : (heisFunctor S ⋙ forget _).RepresentableBy (heisScheme S) where
  homEquiv {T} :=
    { toFun := fun f => (⟨f.left.appTop (AffineSpace.coord S 0), f.left.appTop (AffineSpace.coord S 1),
        f.left.appTop (AffineSpace.coord S 2)⟩ : Heis Γ(T.left, ⊤))
      invFun := fun g : Heis Γ(T.left, ⊤) => Over.homMk (AffineSpace.homOfVector T.hom ![g.a, g.b, g.c])
        (AffineSpace.homOfVector_over _ _)
      left_inv := fun f => Over.OverMorphism.ext (AffineSpace.hom_ext
        ((AffineSpace.homOfVector_over _ _).trans (Over.w f).symm) fun i =>
          (AffineSpace.homOfVector_appTop_coord _ _ i).trans (by fin_cases i <;> rfl))
      right_inv := fun g => Heis.ext (AffineSpace.homOfVector_appTop_coord _ _ 0)
        (AffineSpace.homOfVector_appTop_coord _ _ 1) (AffineSpace.homOfVector_appTop_coord _ _ 2) }
  homEquiv_comp f g := rfl
@[reducible] def heisGrp (S : Scheme.{0}) : GrpObj (heisScheme S) := GrpObj.ofRepresentableBy _ _ (heisRepr S)
attribute [local instance] heisGrp
def heisPt {S : Scheme.{0}} (T : Over S) : (T ⟶ heisScheme S) →* Heis Γ(T.left, ⊤) :=
  ((yonedaGrpObjIsoOfRepresentableBy _ _ (heisRepr S)).hom.app (Opposite.op T)).hom
def heisMk {S : Scheme.{0}} (T : Over S) (a b c : Γ(T.left, ⊤)) : T ⟶ heisScheme S :=
  Over.homMk (AffineSpace.homOfVector T.hom ![a, b, c]) (AffineSpace.homOfVector_over _ _)
end WeilNoncomm
end GlobalTheory


