-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:19:42.634412+00:00
-- url     : https://prove2.me/theorems/6ddadf28-11b2-433f-adfc-36e92fac236f
-- title:
--   Exists Unique Character Of Mul
-- statement:
--   Definitions and structural lemmas for Exists Unique Character Of Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueCharacterOfMul.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace TorusUnit
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)
section Ring
variable {A X : Type} [CommRing A] [AddCommGroup X]
def IsMultiplicative (u : AddMonoidAlgebra A X) : Prop :=
  AddMonoidAlgebra.mapDomainRingHom A ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) u =
    AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inl X X) u *
      AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inr X X) u
end Ring
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
def torusPoint {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (s : Spec R ⟶ S) :
    Over.mk s ⟶ splitTorus S X :=
  Over.homMk (pullback.lift (Spec.map φ) s (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)
variable {Y : Over S}
def prodPoint {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) :
    Spec R ⟶ (splitTorus S X ⊗ Y).left :=
  (lift (torusPoint φ (y ≫ Y.hom)) (Over.homMk y rfl : Over.mk (y ≫ Y.hom) ⟶ Y)).left
def value {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) :
    Γ((splitTorus S X ⊗ Y).left, ⊤) ⟶ R :=
  (prodPoint φ y).appTop ≫ (Scheme.ΓSpecIso R).hom
def IsMulLeft (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) : Prop :=
  ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
    (lift (t * t') y).left.appTop.hom ρ =
      (lift t y).left.appTop.hom ρ * (lift t' y).left.appTop.hom ρ
attribute [local instance] TorusInj.zuAlg
variable (X) in

abbrev grpAlg (R : CommRingCat.{0}) : CommRingCat.{0} := CommRingCat.of (AddMonoidAlgebra R X)
variable (X) in

def fromInt (R : CommRingCat.{0}) : torusRing ZU X ⟶ grpAlg X R :=
  CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra R X))
variable (X) in

def const (R : CommRingCat.{0}) : R ⟶ grpAlg X R :=
  CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))
def expand {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    Γ((splitTorus S X ⊗ Y).left, ⊤) ⟶ grpAlg X R :=
  value (fromInt X R) (Spec.map (const X R) ≫ y)
def IsCharNear (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) (χ : X) (p : Y.left) : Prop :=
  ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
    p ∈ Set.range y ∧ (expand y).hom ρ = single χ 1
end TorusUnit
end GlobalTheory


