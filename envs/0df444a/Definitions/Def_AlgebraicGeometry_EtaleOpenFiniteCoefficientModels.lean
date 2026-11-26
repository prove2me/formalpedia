-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleOpenFiniteCoefficientModels
-- name    : AlgebraicGeometry_EtaleOpenFiniteCoefficientModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T02:40:38.86411+00:00
-- url     : https://prove2.me/theorems/68717994-8eab-586a-873e-6f521a4e9b81
-- title:
--   Extending finite coefficient models from an open
-- statement:
--   A map into a restricted injective prime module sheaf factors through the restriction of an extended finite constant model.
-- source:
--   Mayer–Vietoris and the finite model method for étale cohomology.

import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Limits.VanKampen
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleClosedPushforward (pushforward)

namespace PhilipponEtaleBoundedFiniteModelReduction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- A sheaf embeds in the direct image of a bounded finite constant
sheaf along a finite morphism of finite presentation. -/
def boundedFiniteModel (X : Scheme.{u}) (N : ℕ) : ObjectProperty (Ab X) := fun F =>
  ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : LocallyOfFinitePresentation p)
    (M : AddCommGrpCat.{u}) (_ : Finite M), N • 𝟙 M = 0 ∧
      ∃ m : F ⟶ (pushforward p).obj ((constantSheaf Y.smallEtaleTopology
        AddCommGrpCat.{u}).obj M), Mono m

end PhilipponEtaleBoundedFiniteModelReduction

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
namespace PhilipponEtaleModuleSkyscrapers
universe u
variable {X : Scheme.{u}} {R : Type u} [Ring R]
private abbrev Modules := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)
private abbrev forgetModule := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

private instance : X.smallEtaleTopology.HasSheafCompose (forgetModule (R := R)) where
  isSheaf P hP := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u})
    exact Presheaf.isSheaf_comp_of_isSheaf _ P (CategoryTheory.forget (ModuleCat.{u} R)) hP

/-- Forget the module structure of an étale sheaf. -/
abbrev underlying : Modules (X := X) (R := R) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  sheafCompose X.smallEtaleTopology (forgetModule (R := R))


end PhilipponEtaleModuleSkyscrapers

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite


namespace PhilipponEtaleRelativeCoefficients

universe u

private def liftPresheaf {C : Type*} [Category* C] (N : ℕ)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (h : ∀ U (a : ↥(P.obj U)), N • a = 0) :
    Cᵒᵖ ⥤ ModuleCat.{u} (ZMod N) := by
  letI instModule (U : Cᵒᵖ) : Module (ZMod N) (P.obj U) := AddCommGroup.zmodModule (h U)
  refine {
    obj := fun U => ModuleCat.of (ZMod N) (P.obj U)
    map := fun f => ModuleCat.ofHom ((P.map f).hom.toZModLinearMap N)
    map_id := ?_
    map_comp := ?_ }
  · intro U
    apply ConcreteCategory.hom_ext
    intro a
    change P.map (𝟙 U) a = a
    rw [P.map_id]
    rfl
  · intro U V W f g
    apply ConcreteCategory.hom_ext
    intro a
    change P.map (f ≫ g) a = P.map g (P.map f a)
    rw [P.map_comp]
    rfl

/-- An abelian étale sheaf annihilated by an integer has a model as a
sheaf of modules over the corresponding quotient of the integers. -/
def boundedTorsionModule {X : Scheme.{u}} (N : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (h : N • 𝟙 F = 0) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod N)) := by
  have hSection (W : X.Etaleᵒᵖ) (a : ↥(F.obj.obj W)) : N • a = 0 :=
    congrArg (fun t : F ⟶ F => t.hom.app W a) h
  let P := liftPresheaf N F.obj hSection
  refine ⟨P, ?_⟩
  apply Presheaf.isSheaf_of_isSheaf_comp _ P (forget₂ (ModuleCat.{u} (ZMod N)) AddCommGrpCat.{u})
  exact F.property

/-- The underlying abelian presheaf of the module model is the original
presheaf. -/
theorem boundedTorsionModule_forget {X : Scheme.{u}} (N : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (h : N • 𝟙 F = 0) :
    (boundedTorsionModule N F h).obj ⋙ (forget₂ (ModuleCat.{u} (ZMod N)) AddCommGrpCat.{u}) =
      F.obj := rfl

end PhilipponEtaleRelativeCoefficients

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleModuleSkyscrapers (underlying)
open PhilipponEtaleRelativeCoefficients (boundedTorsionModule boundedTorsionModule_forget)
namespace PhilipponEtalePrimeTorsionComparison
universe u
variable {X : Scheme.{u}}
private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Modules (X : Scheme.{u}) (N : ℕ) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))

theorem underlying_killed {N : ℕ} (J : Modules X N) :
    N • 𝟙 (underlying.obj J) = 0 := by
  have hz : (N : ULift.{u} (ZMod N)) = 0 := ULift.down_injective (ZMod.natCast_self N)
  apply Sheaf.hom_ext
  ext W a
  let b : J.obj.obj W := a
  change N • b = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift.{u} (ZMod N)) N b, hz, zero_smul]

private def modulePresentation (N : ℕ) (F : Ab X) (hF : N • 𝟙 F = 0) :
    Σ M : Modules X N, underlying.obj M ≅ F := by
  let M₀ := boundedTorsionModule N F hF
  let eR : ULift.{u} (ZMod N) ≃+* ZMod N := ULift.ringEquiv
  let liftCoefficients := ModuleCat.restrictScalars.{u} eR.toRingHom
  let : liftCoefficients.IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars.{u} eR.toRingHom).IsEquivalence
  let M : Modules X N :=
    ⟨M₀.obj ⋙ liftCoefficients, Presheaf.isSheaf_comp_of_isSheaf _ _ liftCoefficients M₀.property⟩
  exact ⟨M, (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
    (eqToIso (boundedTorsionModule_forget N F hF))⟩

private def forgetModuleFullyFaithful (N : ℕ) :
    (forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u}).FullyFaithful where
  preimage {A B} a := by
    let a' : A →+ B := a.hom
    refine ModuleCat.ofHom { toAddHom := a', map_smul' := ?_ }
    intro c b
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective c.down
    have h : (m : ULift.{u} (ZMod N)) = c := ULift.down_injective hm
    rw [← h]
    exact map_intCast_smul a' _ _ m b
  map_preimage _ := rfl
  preimage_map a := by
    ext b
    rfl

/-- An injective module sheaf extends abelian sheaf maps along monomorphisms
between sheaves killed by the same integer. -/
theorem exists_extension_of_bounded_mono {N : ℕ} {F M : Ab X} {J : Modules X N} [Injective J]
    (hF : N • 𝟙 F = 0) (hM : N • 𝟙 M = 0)
    (f : F ⟶ underlying.obj J) (a : F ⟶ M) [Mono a] :
    ∃ b : M ⟶ underlying.obj J, a ≫ b = f := by
  let U := underlying (X := X) (R := ULift.{u} (ZMod N))
  let Uf : U.FullyFaithful :=
    fullyFaithfulSheafCompose X.smallEtaleTopology (forgetModuleFullyFaithful N)
  let : U.Faithful := Uf.faithful
  obtain ⟨F', eF⟩ := modulePresentation N F hF
  obtain ⟨M', eM⟩ := modulePresentation N M hM
  let c : U.obj F' ⟶ U.obj M' := eF.hom ≫ a ≫ eM.inv
  let : Mono c := mono_comp eF.hom (a ≫ eM.inv)
  let c' := Uf.preimage c
  have hc : U.map c' = c := Uf.map_preimage c
  have hcMono : Mono (U.map c') := by rw [hc]; exact inferInstanceAs (Mono c)
  let : Mono c' := Functor.mono_of_mono_map U hcMono
  let f' := Uf.preimage (eF.hom ≫ f)
  let b' := Injective.factorThru f' c'
  have h : c ≫ U.map b' = eF.hom ≫ f := by
    rw [← hc, ← U.map_comp, Injective.comp_factorThru, Uf.map_preimage]
  exact ⟨eM.inv ≫ U.map b', (cancel_epi eF.hom).mp (by
    simpa only [c, Category.assoc] using h)⟩


end PhilipponEtalePrimeTorsionComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)


namespace PhilipponEtaleClosedFiberDegreeOne

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Coeff (N : ℕ) := ModuleCat.{u} (ULift.{u} (ZMod N))
private abbrev Modules (X : Scheme.{u}) (N : ℕ) := Sheaf X.smallEtaleTopology (Coeff N)
private abbrev constant (X : Scheme.{u}) (M : AddCommGrpCat.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M

/-- The finite direct-image model with constant prime cyclic coefficients. -/
abbrev finiteConstantModel {X Y : Scheme.{u}} (p : Y ⟶ X) (N : ℕ) : Ab X :=
  (pushforward p).obj (constant Y (AddCommGrpCat.of (ULift.{u} (ZMod N))))

end PhilipponEtaleClosedFiberDegreeOne

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponEtaleConstantDegreeZero

universe u
variable (X : Scheme.{u}) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private def constantMap : (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of A) ⟶
    (continuousSheaf X A).obj where
  app W := AddCommGrpCat.ofHom
    { toFun := fun a => ContinuousMap.const W.unop.left a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality := by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro a
    apply ContinuousMap.ext
    intro x
    rfl

private theorem constantMap_locallyInjective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantMap X A) := by
  constructor
  intro W a b hab
  by_cases h : a = b
  · subst b
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact X.smallEtaleTopology.top_mem _
  · have hW : IsEmpty W.unop.left := ⟨fun x => h (congrArg (fun f : C(W.unop.left, A) => f x) hab)⟩
    let V : Fin 0 → X.Etale := fun _ => W.unop
    let r : ∀ i, V i ⟶ W.unop := fun _ => 𝟙 W.unop
    have hcover : Sieve.ofArrows V r ∈ X.smallEtaleTopology W.unop :=
      (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr (Set.eq_univ_of_forall fun x => isEmptyElim x)
    apply X.smallEtaleTopology.superset_covering _ hcover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Fin.elim0 i

private theorem constantMap_locallySurjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantMap X A) := by
  constructor
  intro W s
  change C(W.left, A) at s
  let U (a : A) : W.left.Opens := ⟨s ⁻¹' {a}, (isOpen_discrete {a}).preimage s.continuous⟩
  let V (a : A) := Scheme.Etale.mk ((U a).ι ≫ W.hom)
  let r (a : A) : V a ⟶ W := MorphismProperty.Over.homMk (U a).ι rfl
  have hcover : Sieve.ofArrows V r ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨s x, ⟨⟨x, rfl⟩, rfl⟩⟩
  apply X.smallEtaleTopology.superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨a⟩
  refine ⟨a, ?_⟩
  apply ContinuousMap.ext
  intro x
  exact x.property.symm

/-- For discrete coefficients, sheafifying constant functions gives the
small étale sheaf of continuous functions. -/
def constantSheafIso : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of A) ≅ continuousSheaf X A := by
  let J := X.smallEtaleTopology
  let G := presheafToSheaf J AddCommGrpCat.{u}
  have h := (J.W_iff_isLocallyBijective (constantMap X A)).mpr
    ⟨constantMap_locallyInjective X A, constantMap_locallySurjective X A⟩
  let : IsIso (G.map (constantMap X A)) := (J.W_iff _).mp h
  exact (asIso (G.map (constantMap X A))).trans (sheafificationIso (continuousSheaf X A)).symm

end PhilipponEtaleConstantDegreeZero

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteSchemeCoproduct

universe u

variable {I : Type u} {X : Scheme.{u}} {Y : I → Scheme.{u}} (p : ∀ i, Y i ⟶ X)

/-- A finite coproduct of finite morphisms to an affine scheme is finite. -/
theorem isFinite_sigmaDesc [Finite I] [IsAffine X] [∀ i, IsFinite (p i)] :
    IsFinite (Sigma.desc p) := by
  let : ∀ i, IsAffine (Y i) := fun i => isAffine_of_isAffineHom (p i)
  let R := Γ(X, ⊤)
  let S (i : I) := Γ(Y i, ⊤)
  let : ∀ i, Algebra R (S i) := fun i => (p i).appTop.hom.toAlgebra
  let : ∀ i, Module.Finite R (S i) := fun i => (p i).finite_appTop
  let a : R ⟶ CommRingCat.of (∀ i, S i) := CommRingCat.ofHom (algebraMap R (∀ i, S i))
  let e := (Sigma.mapIso fun i => (Y i).isoSpec) ≪≫ asIso (sigmaSpec S)
  let : IsFinite (Spec.map a) := (IsFinite.SpecMap_iff a).2 (RingHom.finite_algebraMap.mpr inferInstance)
  have he : Sigma.desc p = e.hom ≫ Spec.map a ≫ X.isoSpec.inv := by
    apply Sigma.hom_ext
    intro i
    simp only [e, Sigma.ι_desc, Iso.trans_hom, asIso_hom, Category.assoc, Sigma.ι_mapIso_hom_assoc]
    change p i = (Y i).isoSpec.hom ≫ Sigma.ι (fun j => Spec (S j)) i ≫
      sigmaSpec S ≫ Spec.map a ≫ X.isoSpec.inv
    rw [ι_sigmaSpec_assoc, ← Spec.map_comp_assoc]
    have h : a ≫ CommRingCat.ofHom (Pi.evalRingHom (S ·) i) = (p i).appTop := by
      apply CommRingCat.hom_ext
      ext x
      rfl
    rw [h, Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  rw [he]
  infer_instance

/-- Local finite presentation can be checked on the coproduct inclusions. -/
theorem locallyOfFinitePresentation_sigmaDesc [∀ i, LocallyOfFinitePresentation (p i)] :
    LocallyOfFinitePresentation (Sigma.desc p) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) (sigmaOpenCover Y)
  intro i
  change LocallyOfFinitePresentation (Sigma.ι Y i ≫ Sigma.desc p)
  rw [Sigma.ι_desc]
  infer_instance

/-- The inclusion of a component after base change of the coproduct. -/
def pullbackInclusion {T : Scheme.{u}} (f : T ⟶ X) (i : I) :
    pullback f (p i) ⟶ pullback f (Sigma.desc p) :=
  pullback.lift (pullback.fst f (p i)) (pullback.snd f (p i) ≫ Sigma.ι Y i) (by
    rw [Category.assoc, Sigma.ι_desc, pullback.condition])

@[reassoc (attr := simp)]
theorem pullbackInclusion_fst {T : Scheme.{u}} (f : T ⟶ X) (i : I) :
    pullbackInclusion p f i ≫ pullback.fst f (Sigma.desc p) = pullback.fst f (p i) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackInclusion_snd {T : Scheme.{u}} (f : T ⟶ X) (i : I) :
    pullbackInclusion p f i ≫ pullback.snd f (Sigma.desc p) =
      pullback.snd f (p i) ≫ Sigma.ι Y i :=
  pullback.lift_snd _ _ _

/-- The pullback of a finite coproduct is the coproduct of the pullbacks. -/
def pullbackCoproductIso [Finite I] {T : Scheme.{u}} (f : T ⟶ X) :
    (∐ fun i => pullback f (p i)) ≅ pullback f (Sigma.desc p) := by
  let a := FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)
  let h := (a.nonempty_isColimit_of_isPullback_left p (Sigma.desc p) f
    (fun i => pullback.fst f (p i)) (fun i => pullback.snd f (p i))
    (fun i => IsPullback.of_hasPullback f (p i)) (IsPullback.of_hasPullback f (Sigma.desc p))
    (Cofan.mk _ (pullbackInclusion p f)) (Iso.refl _) (by simp) (by simp) (by simp)).some
  exact (coproductIsCoproduct (fun i => pullback f (p i))).coconePointUniqueUpToIso h

@[reassoc (attr := simp)]
theorem ι_pullbackCoproductIso [Finite I] {T : Scheme.{u}} (f : T ⟶ X) (i : I) :
    Sigma.ι (fun i => pullback f (p i)) i ≫ (pullbackCoproductIso p f).hom =
      pullbackInclusion p f i := by
  unfold pullbackCoproductIso
  exact (coproductIsCoproduct (fun i => pullback f (p i))).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

/-- A finite coproduct of finite morphisms to a scheme is finite. -/
theorem isFinite_sigmaDesc_of_finite [Finite I] [∀ i, IsFinite (p i)] :
    IsFinite (Sigma.desc p) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) X.affineCover).2 fun j => ?_
  let T := X.affineCover.X j
  let f : T ⟶ X := X.affineCover.f j
  let e := pullbackCoproductIso p f
  let a (i : I) := pullback.fst f (p i)
  let : ∀ i, IsFinite (a i) := fun i => by dsimp [a]; infer_instance
  let : IsFinite (Sigma.desc a) := isFinite_sigmaDesc a
  have he : e.hom ≫ pullback.fst f (Sigma.desc p) = Sigma.desc a := by
    apply Sigma.hom_ext
    intro i
    rw [ι_pullbackCoproductIso_assoc, pullbackInclusion_fst, Sigma.ι_desc]
  have h : pullback.fst f (Sigma.desc p) = e.inv ≫ Sigma.desc a := by
    rw [← he, Iso.inv_hom_id_assoc]
  change IsFinite (pullback.snd (Sigma.desc p) f)
  rw [← pullbackSymmetry_hom_comp_fst, h]
  infer_instance

end PhilipponFiniteSchemeCoproduct

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (constantSheafIso continuousSheaf)
open PhilipponFiniteSchemeCoproduct


namespace PhilipponEtaleFiniteModelCoproduct

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {I : Type u} [Finite I] {X : Scheme.{u}} {Y : I → Scheme.{u}}
  (p : ∀ i, Y i ⟶ X) (M : I → AddCommGrpCat.{u})

local instance (i : I) : TopologicalSpace (M i) := ⊥
local instance (i : I) : DiscreteTopology (M i) := ⟨rfl⟩
local instance : TopologicalSpace (∀ i, M i) := ⊥
local instance : DiscreteTopology (∀ i, M i) := ⟨rfl⟩

private abbrev atComponent (i : I) := (pushforward (p i)).obj (continuousSheaf (Y i) (M i))
private abbrev fiber {Y : Scheme.{u}} (p : Y ⟶ X) (W : X.Etale) : Scheme.{u} :=
  pullback W.hom p

private def baseHomeo (W : X.Etale) :
    (Σ i, fiber (p i) W) ≃ₜ fiber (Sigma.desc p) W :=
  (sigmaMk (fun i => fiber (p i) W)).trans (pullbackCoproductIso p W.hom).hom.homeomorph

private theorem baseHomeo_mk (W : X.Etale) (i : I) (z : fiber (p i) W) :
    baseHomeo p W ⟨i, z⟩ = pullbackInclusion p W.hom i z := by
  change (pullbackCoproductIso p W.hom).hom (sigmaMk _ ⟨i, z⟩) = _
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_pullbackCoproductIso]

private abbrev chartMap {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    fiber r U ⟶ fiber r V := ((baseChange r).map a).left

@[reassoc]
private theorem chartMap_fst {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    chartMap r a ≫ pullback.fst V.hom r = pullback.fst U.hom r ≫ a.left :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem chartMap_snd {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    chartMap r a ≫ pullback.snd V.hom r = pullback.snd U.hom r :=
  pullback.lift_snd _ _ _

omit [Finite I] in
private theorem chartMap_inclusion {U V : X.Etale} (a : U ⟶ V) (i : I) :
    pullbackInclusion p U.hom i ≫ chartMap (Sigma.desc p) a =
      chartMap (p i) a ≫ pullbackInclusion p V.hom i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, chartMap_fst, pullbackInclusion_fst_assoc, pullbackInclusion_fst]
  · simp only [Category.assoc, chartMap_snd, pullbackInclusion_snd, chartMap_snd_assoc]

variable {F : Ab X} (m : ∀ i, F ⟶ atComponent p M i)

private abbrev componentSection (i : I) (W : X.Etale) (s : F.obj.obj (op W)) :
    C(fiber (p i) W, M i) := (m i).hom.app (op W) s

variable {B : AddCommGrpCat.{u}} [TopologicalSpace B] [DiscreteTopology B]
  (l : ∀ i, M i ⟶ B)

private def assembled (W : X.Etale) (s : F.obj.obj (op W)) :
    C(fiber (Sigma.desc p) W, B) := by
  let a (i : I) := componentSection p M m i W s
  let k (z : Σ i, fiber (p i) W) : B := l z.1 (a z.1 z.2)
  have hk : Continuous k := continuous_sigma fun i =>
    (continuous_of_discreteTopology (f := l i)).comp (a i).continuous
  exact ⟨k ∘ (baseHomeo p W).symm, hk.comp (baseHomeo p W).symm.continuous⟩

omit [DiscreteTopology B] in
private theorem assembled_component (W : X.Etale) (s : F.obj.obj (op W)) (i : I)
    (z : fiber (p i) W) :
    assembled p M m l W s (pullbackInclusion p W.hom i z) =
      l i (componentSection p M m i W s z) := by
  rw [← baseHomeo_mk]
  exact congrArg (fun t : Σ j, fiber (p j) W =>
    l t.1 (componentSection p M m t.1 W s t.2))
    ((baseHomeo p W).symm_apply_apply ⟨i, z⟩)

private def combined : F ⟶ (pushforward (Sigma.desc p)).obj (continuousSheaf (∐ Y) B) := by
  classical
  refine ⟨{
    app := fun W => AddCommGrpCat.ofHom {
      toFun := assembled p M m l W.unop
      map_zero' := ?_
      map_add' := fun s t => ?_ }
    naturality := ?_ }⟩
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p W.unop).surjective z
    simp only [baseHomeo_mk, assembled_component, componentSection, map_zero,
      ContinuousMap.zero_apply]
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p W.unop).surjective z
    rw [baseHomeo_mk, assembled_component]
    change l i (componentSection p M m i W.unop (s + t) w) =
      assembled p M m l W.unop s _ + assembled p M m l W.unop t _
    have hm : componentSection p M m i W.unop (s + t) =
        componentSection p M m i W.unop s + componentSection p M m i W.unop t :=
      ((m i).hom.app (op W.unop)).hom.map_add s t
    rw [assembled_component, assembled_component, hm, ContinuousMap.add_apply, map_add]
  · intro U V a
    apply ConcreteCategory.hom_ext
    intro s
    apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p V.unop).surjective z
    rw [baseHomeo_mk]
    let b := chartMap (Sigma.desc p) a.unop
    let bᵢ := chartMap (p i) a.unop
    have h : b (pullbackInclusion p V.unop.hom i w) =
        pullbackInclusion p U.unop.hom i (bᵢ w) :=
      congrArg (fun d : fiber (p i) V.unop ⟶ fiber (Sigma.desc p) U.unop => d w)
        (chartMap_inclusion p a.unop i)
    change assembled p M m l V.unop (F.obj.map a s) (pullbackInclusion p V.unop.hom i w) =
      assembled p M m l U.unop s (b (pullbackInclusion p V.unop.hom i w))
    rw [h, assembled_component, assembled_component]
    have hm := ConcreteCategory.congr_hom ((m i).hom.naturality a) s
    exact congrArg (fun c : C(fiber (p i) V.unop, M i) => l i (c w)) hm

/-- Coefficient homomorphisms that jointly detect sections can be assembled into
a single map to the constant direct image on the coproduct. -/
private theorem mono_combined
    (h : ∀ (G : Ab X) (a b : G ⟶ F),
      (∀ i W s z, l i (componentSection p M m i W (a.hom.app (op W) s) z) =
        l i (componentSection p M m i W (b.hom.app (op W) s) z)) → a = b) :
    Mono (combined p M m l) := by
  refine ⟨fun {G} a b e => h G a b fun i W s z => ?_⟩
  have eW := ConcreteCategory.congr_hom (congrArg (fun g => g.hom.app (op W)) e) s
  have ev := congrArg (fun c : C(fiber (Sigma.desc p) W, B) =>
    c (pullbackInclusion p W.hom i z)) eW
  change assembled p M m l W (a.hom.app (op W) s) _ =
    assembled p M m l W (b.hom.app (op W) s) _ at ev
  simpa only [assembled_component] using ev

private theorem exists_prime_coordinates {A : Type u} [AddCommGroup A] [Finite A]
    {N : ℕ} (hN : N.Prime) (hA : ∀ x : A, N • x = 0) :
    ∃ n : ℕ, Nonempty (A ≃+ (Fin n → ZMod N)) := by
  letI : Fact N.Prime := ⟨hN⟩
  letI scalar : Module (ZMod N) A := AddCommGroup.zmodModule hA
  let finite := @Module.Finite.of_finite (ZMod N) A inferInstance inferInstance scalar inferInstance
  let b := @Module.finBasis (ZMod N) A inferInstance inferInstance scalar
    (Module.Free.of_divisionRing (ZMod N) A) inferInstance finite
  exact ⟨_, ⟨b.equivFun.toAddEquiv⟩⟩

/-- A finite direct image with finite prime-annihilated coefficients embeds in a
finite direct image with coefficients in the corresponding prime field. -/
theorem exists_mono_prime_constant_directImage {T : Scheme.{u}} (q : T ⟶ X) [IsFinite q]
    (A : AddCommGrpCat.{u}) [Finite A] (N : ℕ) (hN : N.Prime)
    (hA : N • 𝟙 A = 0) :
    ∃ (Z : Scheme.{u}) (r : Z ⟶ X) (_ : IsFinite r)
      (g : (pushforward q).obj ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u}).obj A) ⟶
        (pushforward r).obj ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} (ZMod N))))), Mono g := by
  obtain ⟨n, ⟨b⟩⟩ := exists_prime_coordinates hN fun x : A => ConcreteCategory.congr_hom hA x
  let I := ULift.{u} (Fin n)
  let B := AddCommGrpCat.of (ULift.{u} (ZMod N))
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  let p : I → (T ⟶ X) := fun _ => q
  let l (i : I) : A ⟶ B := AddCommGrpCat.ofHom {
    toFun := fun x => ULift.up (b x i.down)
    map_zero' := congrArg (fun c => ULift.up (c i.down)) b.map_zero
    map_add' := fun x y => congrArg (fun c => ULift.up (c i.down)) (b.map_add x y) }
  let F := (pushforward q).obj (continuousSheaf T A)
  let m (i : I) : F ⟶ atComponent p (fun _ => A) i := 𝟙 F
  let k := combined p (fun _ => A) m l
  letI : Mono k := mono_combined p (fun _ => A) m l fun G a c h => by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro s
    apply ContinuousMap.ext
    intro z
    apply b.injective
    funext i
    exact congrArg ULift.down (h ⟨i⟩ W.unop s z)
  letI : ∀ i : I, IsFinite (p i) := fun _ => inferInstanceAs (IsFinite q)
  let e := (pushforward q).mapIso (constantSheafIso T A)
  let f := (pushforward (Sigma.desc p)).mapIso
    (constantSheafIso (∐ fun _ : I => T) B)
  exact ⟨∐ fun _ : I => T, Sigma.desc p, isFinite_sigmaDesc_of_finite p,
    e.hom ≫ k ≫ f.inv, inferInstance⟩

end PhilipponEtaleFiniteModelCoproduct

end

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleClosedFiberDegreeOne (finiteConstantModel)
open PhilipponEtaleExtensionByZero (restrict exists_extension_of_restriction_mono)
open PhilipponEtaleFiniteModelCoproduct (exists_mono_prime_constant_directImage)
open PhilipponEtaleModuleSkyscrapers (underlying)
open PhilipponEtalePrimeTorsionComparison (exists_extension_of_bounded_mono)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtaleFiniteConstantApproximation

universe u

private abbrev Coeff (N : ℕ) := ModuleCat.{u} (ULift.{u} (ZMod N))
private abbrev Modules (X : Scheme.{u}) (N : ℕ) := Sheaf X.smallEtaleTopology (Coeff N)
private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private theorem finiteConstantModel_killed {X Y : Scheme.{u}} (p : Y ⟶ X) (N : ℕ) :
    N • 𝟙 (finiteConstantModel p N) = 0 := by
  let A := AddCommGrpCat.of (ULift.{u} (ZMod N))
  let C := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 Y)) :=
    IsTerminal.isTerminalOfObj (Scheme.Etale.forget Y) _ Over.mkIdTerminal
  let : C.Additive :=
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} hT).left_adjoint_additive
  let P := pushforward p
  let : P.Additive := (pullbackAdjunction p).right_adjoint_additive
  let D := C ⋙ P
  have hA : N • 𝟙 A = 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.down_injective
    change N • x.down = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  change N • 𝟙 (D.obj A) = 0
  simpa only [D.map_nsmul, D.map_id, D.map_zero] using congrArg (fun f => D.map f) hA

private theorem killed_of_mono {X : Scheme.{u}} {F M : Ab X}
    {N : ℕ} (d : F ⟶ M) [Mono d] (hM : N • 𝟙 M = 0) :
    N • 𝟙 F = 0 := (cancel_mono d).mp (by
  calc
    (N • 𝟙 F) ≫ d = N • d := by rw [Preadditive.nsmul_comp, Category.id_comp]
    _ = d ≫ (N • 𝟙 M) := by rw [Preadditive.comp_nsmul, Category.comp_id]
    _ = (0 : F ⟶ F) ≫ d := by rw [hM, comp_zero, zero_comp])

/-- Maps on an open from a bounded finite model into a restricted injective
coefficient sheaf factor through a finite constant model on the ambient scheme
if finite schemes over the open have finite extensions. -/
theorem exists_factorization_on_open {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    {N : ℕ} (hN : N.Prime) {J : Modules X N} [Injective J]
    (hExtend : ∀ {T : Scheme.{u}} (q : T ⟶ W) [IsFinite q],
      ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (k : T ⟶ Y), IsPullback q k j p)
    {F : Ab W} (hF : boundedFiniteModel W N F) (f : F ⟶ (restrict j).obj (underlying.obj J)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p)
      (a : finiteConstantModel p N ⟶ underlying.obj J)
      (b : F ⟶ (restrict j).obj (finiteConstantModel p N)), b ≫ (restrict j).map a = f := by
  obtain ⟨T, q, hq, _, A, hA, hNA, g, hg⟩ := hF
  let : IsFinite q := hq
  let : Finite A := hA
  obtain ⟨T', q', hq', c, hc⟩ := exists_mono_prime_constant_directImage q A N hN hNA
  let : IsFinite q' := hq'
  obtain ⟨Y, p, hp, k, hk⟩ := hExtend q'
  let : IsOpenImmersion k := MorphismProperty.of_isPullback hk inferInstance
  let B := finiteConstantModel p N
  let e : (restrict j).obj B ≅ finiteConstantModel q' N :=
    PhilipponEtaleOpenDirectImage.restrictConstantDirectImageIso j p q' k hk
      (AddCommGrpCat.of (ULift.{u} (ZMod N)))
  let : Mono g := hg
  let : Mono c := hc
  let m : F ⟶ (restrict j).obj B := g ≫ c ≫ e.inv
  let : Mono m := mono_comp g (c ≫ e.inv)
  obtain ⟨H, u, a, hMono, _, hFactor⟩ := exists_extension_of_restriction_mono j m
  obtain ⟨b, hb⟩ := hFactor _ f
  let : Mono a := hMono
  have hB := finiteConstantModel_killed p N
  obtain ⟨a', ha'⟩ := exists_extension_of_bounded_mono (killed_of_mono a hB) hB b a
  refine ⟨Y, p, hp, a', u ≫ (restrict j).map a, ?_⟩
  rw [Category.assoc, ← (restrict j).map_comp, ha', hb]

end PhilipponEtaleFiniteConstantApproximation

end

end


