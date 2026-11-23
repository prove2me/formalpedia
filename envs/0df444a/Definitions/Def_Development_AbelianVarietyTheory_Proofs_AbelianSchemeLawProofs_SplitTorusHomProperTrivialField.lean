-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:25.483982+00:00
-- url     : https://prove2.me/theorems/55b3b06b-8021-4dd2-8f33-7efa42169483
-- title:
--   Split Torus Hom Proper Trivial Field
-- statement:
--   Definitions and structural lemmas for Split Torus Hom Proper Trivial Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomProperTrivialField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace TorusToProper
variable {K : Type} [Field K]
noncomputable abbrev sp (K : Type) [Field K] (R : Type) [CommRing R] [Algebra K R] :
    Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R)))
noncomputable def spm {R R' : Type} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    (g : R →ₐ[K] R') : sp K R' ⟶ sp K R :=
  Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp)
lemma mul_left_fst {S S' A : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {a : A ⟶ S'} {c : A ⟶ S}
    (x y : Over.mk a ⟶ (Over.pullback f).obj G) (x₀ y₀ : Over.mk c ⟶ G)
    (hx : x₀.left = x.left ≫ pullback.fst G.hom f) (hy : y₀.left = y.left ≫ pullback.fst G.hom f) :
    (x * y).left ≫ pullback.fst G.hom f = (x₀ * y₀).left := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk a ⟶ (Over.pullback f).obj (G ⊗ G) :=
    lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl
variable (K) (X : Type) [AddCommGroup X]
noncomputable def charAlg (R : Type) [CommRing R] (φ : Multiplicative X →* Rˣ) :
    letI : Algebra (ULift.{0} ℤ) R := ULift.algebra' ℤ R
    AddMonoidAlgebra (ULift.{0} ℤ) X →ₐ[ULift.{0} ℤ] R :=
  letI : Algebra (ULift.{0} ℤ) R := ULift.algebra' ℤ R
  AddMonoidAlgebra.lift (ULift.{0} ℤ) R X ((Units.coeHom R).comp φ)
noncomputable def charRing (R : Type) [CommRing R] (φ : Multiplicative X →* Rˣ) :
    AddMonoidAlgebra (ULift.{0} ℤ) X →+* R :=
  letI : Algebra (ULift.{0} ℤ) R := ULift.algebra' ℤ R
  (charAlg X R φ).toRingHom
noncomputable def ptFun (R : Type) [CommRing R] [Algebra K R] (φ : Multiplicative X →* Rˣ) :
    sp K R ⟶ splitTorus (Spec (CommRingCat.of K)) X :=
  Over.homMk (pullback.lift (Spec.map (CommRingCat.ofHom (charRing X R φ)) :
    _ ⟶ (splitTorusAff ZU X).left) (sp K R).hom (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)
lemma ptFun_fst (R : Type) [CommRing R] [Algebra K R] (φ : Multiplicative X →* Rˣ) :
    (ptFun K X R φ).left ≫ Rosenlicht.torusFst _ X = Spec.map (CommRingCat.ofHom (charRing X R φ)) :=
  pullback.lift_fst _ _ _
variable {K X} in
lemma torus_ext {Z : Over (Spec (CommRingCat.of K))} {t t' : Z ⟶ splitTorus (Spec (CommRingCat.of K)) X}
    (h : t.left ≫ Rosenlicht.torusFst _ X = t'.left ≫ Rosenlicht.torusFst _ X) : t = t' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w t).trans (Over.w t').symm
lemma ptFun_mul (R : Type) [CommRing R] [Algebra K R] (φ ψ : Multiplicative X →* Rˣ) :
    ptFun K X R (φ * ψ) = ptFun K X R φ * ptFun K X R ψ := by
  letI : Algebra (ULift.{0} ℤ) R := ULift.algebra' ℤ R
  apply torus_ext
  have h := mul_left_fst (toZ (Spec (CommRingCat.of K))) (splitTorusAff ZU X)
    (ptFun K X R φ) (ptFun K X R ψ)
    (Spec.mapMulEquiv (WithConv.toConv (charAlg X R φ)))
    (Spec.mapMulEquiv (WithConv.toConv (charAlg X R ψ)))
    (ptFun_fst K X R φ).symm (ptFun_fst K X R ψ).symm
  have h2 : WithConv.toConv (charAlg X R φ) * WithConv.toConv (charAlg X R ψ) =
      WithConv.toConv (charAlg X R (φ * ψ)) := by
    apply WithConv.ofConv_injective
    apply AddMonoidAlgebra.algHom_ext
    · intro a
      simp [AlgHom.convMul_apply, charAlg]
    · exact Subsingleton.elim _ _
  have h3 := (Spec.mapMulEquiv (R := ULift.{0} ℤ) (S := AddMonoidAlgebra (ULift.{0} ℤ) X) (T := R)).map_mul
    (WithConv.toConv (charAlg X R φ)) (WithConv.toConv (charAlg X R ψ))
  rw [h2] at h3
  rw [ptFun_fst]
  exact (congrArg CommaMorphism.left h3).trans h.symm
noncomputable def pt (R : Type) [CommRing R] [Algebra K R] :
    (Multiplicative X →* Rˣ) →* (sp K R ⟶ splitTorus (Spec (CommRingCat.of K)) X) :=
  MonoidHom.mk' (ptFun K X R) (ptFun_mul K X R)
noncomputable def univ : Multiplicative X →* (AddMonoidAlgebra K X)ˣ :=
  (AddMonoidAlgebra.of K X).toHomUnits
variable {X} in

def coch (l : X →+ ℤ) (G : Type) [CommGroup G] : G →* (Multiplicative X →* G) where
  toFun x :=
    { toFun := fun a => x ^ l a.toAdd
      map_one' := by simp
      map_mul' := fun a b => by simp [zpow_add] }
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_zpow]
end TorusToProper
end GlobalTheory


