-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isZero_etale_higherDirectImage_of_prime_injective_projective_base_change
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T02:29:42.52212+00:00
-- url     : https://prove2.me/submissions/a58b8a70-98b0-4416-97b5-1d82eda1db9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.ZMod
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Theorems.Thm_AlgebraicGeometry_Scheme_etale_pushforward_preservesFiniteColimits_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_surjective_projectiveLinePower_cover
import Theorems.Thm_AlgebraicGeometry_Scheme_isZero_etale_higherDirectImage_of_prime_injective_projectiveLine_base_change
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_directImage_baseChange_of_isProper

set_option maxHeartbeats 1400000

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
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

/-- Forgetting module structure preserves finite limits of étale sheaves. -/
theorem underlying_preservesFiniteLimits :
    PreservesFiniteLimits (underlying (X := X) (R := R)) := by
  let U := forgetModule (R := R)
  let F := underlying (X := X) (R := R)
  let S := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let T := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} R)
  have : PreservesFiniteLimits (F ⋙ S) :=
    inferInstanceAs (PreservesFiniteLimits
      (T ⋙ (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj U))
  exact preservesFiniteLimits_of_reflects_of_preserves F S

end PhilipponEtaleModuleSkyscrapers

end

section

set_option autoImplicit false
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleModuleSkyscrapers (underlying underlying_preservesFiniteLimits)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleRelativeCoefficients (boundedTorsionModule boundedTorsionModule_forget)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtalePrimeTorsionComparison

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
variable {X Y : Scheme.{u}} (f : Y ⟶ X)
private abbrev Modules (X : Scheme.{u}) (N : ℕ) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))

private theorem underlying_killed {N : ℕ} (J : Modules X N) :
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

private theorem exists_injective_module_embedding (N : ℕ)
    (F : Ab X) (hF : N • 𝟙 F = 0) :
    ∃ (J : Modules X N) (_ : Injective J) (i : F ⟶ underlying.obj J), Mono i := by
  let U := underlying (X := X) (R := ULift.{u} (ZMod N))
  have : PreservesFiniteLimits U := underlying_preservesFiniteLimits
  obtain ⟨M, e⟩ := modulePresentation N F hF
  exact ⟨Injective.under M, inferInstance, e.inv ≫ U.map (Injective.ι M), inferInstance⟩

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

/-- Direct image on étale sheaves with module coefficients. -/
def modulePushforward (N : ℕ) : Modules Y N ⥤ Modules X N :=
  (baseChange f).sheafPushforwardContinuous (ModuleCat.{u} (ULift.{u} (ZMod N)))
    X.smallEtaleTopology Y.smallEtaleTopology

/-- Forgetting coefficients commutes with the étale direct image. -/
def underlyingPushforwardIso (N : ℕ) (K : Modules Y N) :
    underlying.obj ((modulePushforward f N).obj K) ≅
      (pushforward f).obj (underlying.obj K) :=
  (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso (Iso.refl _)

private theorem pullback_underlying_killed (N : ℕ) (J : Modules X N) :
    N • 𝟙 ((pullbackSheaves f).obj (underlying.obj J)) = 0 := by
  let L : Ab X ⥤ Ab Y := pullbackSheaves f
  let : L.Additive := (pullbackAdjunction f).left_adjoint_additive
  let G : Ab X := underlying.obj J
  change N • 𝟙 (L.obj G) = 0
  calc
    _ = L.map (N • 𝟙 G) := by simp only [L.map_nsmul, L.map_id]
    _ = _ := by rw [show N • 𝟙 G = 0 from underlying_killed J, L.map_zero]

set_option maxHeartbeats 800000 in
/-- Direct image along a scheme morphism preserves injective sheaves of
modules over the constant coefficient ring `ℤ/Nℤ`. -/
theorem injective_modulePushforward (N : ℕ) (K : Modules Y N) [Injective K] :
    Injective ((modulePushforward f N).obj K) := by
  constructor
  intro A B a m hm
  let L : Ab X ⥤ Ab Y := pullbackSheaves f
  let U := underlying (X := X) (R := ULift.{u} (ZMod N))
  let V := underlying (X := Y) (R := ULift.{u} (ZMod N))
  let Uf : U.FullyFaithful :=
    fullyFaithfulSheafCompose X.smallEtaleTopology (forgetModuleFullyFaithful N)
  let Vf : V.FullyFaithful :=
    fullyFaithfulSheafCompose Y.smallEtaleTopology (forgetModuleFullyFaithful N)
  let : V.Faithful := Vf.faithful
  let : PreservesFiniteLimits U := underlying_preservesFiniteLimits
  let : PreservesFiniteLimits L := inferInstanceAs (PreservesFiniteLimits (pullbackSheaves f))
  let : Mono (U.map m) := Functor.map_mono U m
  let : Mono (L.map (U.map m)) := Functor.map_mono L (U.map m)
  let adj : L ⊣ pushforward f := pullbackAdjunction f
  let e := underlyingPushforwardIso f N K
  let a' := (adj.homEquiv (U.obj A) (V.obj K)).symm (U.map a ≫ e.hom)
  obtain ⟨A', eA⟩ := modulePresentation N (L.obj (U.obj A)) (pullback_underlying_killed f N A)
  obtain ⟨B', eB⟩ := modulePresentation N (L.obj (U.obj B)) (pullback_underlying_killed f N B)
  let l : V.obj A' ⟶ V.obj B' := eA.hom ≫ L.map (U.map m) ≫ eB.inv
  let : Mono l := mono_comp eA.hom (L.map (U.map m) ≫ eB.inv)
  let lM : A' ⟶ B' := Vf.preimage l
  have hl : V.map lM = l := Vf.map_preimage l
  have hlMono : Mono (V.map lM) := by rw [hl]; exact inferInstanceAs (Mono l)
  let : Mono lM := Functor.mono_of_mono_map V hlMono
  let aM : A' ⟶ K := Vf.preimage (eA.hom ≫ a')
  let r : B' ⟶ K := Injective.factorThru aM lM
  let t : L.obj (U.obj B) ⟶ V.obj K := eB.inv ≫ V.map r
  have hr : l ≫ V.map r = eA.hom ≫ a' := by
    rw [← hl, ← V.map_comp, Injective.comp_factorThru]
    exact Vf.map_preimage _
  have ht : L.map (U.map m) ≫ t = a' := by
    apply (cancel_epi eA.hom).mp
    simpa only [l, t, Category.assoc] using hr
  let b := adj.homEquiv (U.obj B) (V.obj K) t
  refine ⟨Uf.preimage (b ≫ e.inv), Uf.map_injective ?_⟩
  rw [U.map_comp, Uf.map_preimage]
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change U.map m ≫ adj.homEquiv _ _ t = U.map a ≫ e.hom
  rw [← adj.homEquiv_naturality_left, ht]
  exact (adj.homEquiv (U.obj A) (V.obj K)).apply_symm_apply _

set_option maxHeartbeats 600000 in
/-- An injective module sheaf is a retract of the direct image of an injective
module sheaf along any surjective scheme morphism. -/
theorem exists_directImage_retraction [Surjective f] (N : ℕ)
    (J : Modules X N) [Injective J] :
    ∃ (K : Modules Y N) (_ : Injective K)
      (a : underlying.obj J ⟶ (pushforward f).obj (underlying.obj K))
      (b : (pushforward f).obj (underlying.obj K) ⟶ underlying.obj J), a ≫ b = 𝟙 _ := by
  let L : Ab X ⥤ Ab Y := pullbackSheaves f
  let U := underlying (X := X) (R := ULift.{u} (ZMod N))
  let G : Ab X := U.obj J
  have h : N • 𝟙 (L.obj G) = 0 := pullback_underlying_killed f N J
  obtain ⟨K, hK, a, ha⟩ := exists_injective_module_embedding N (L.obj G) h
  let : Mono a := ha
  let : Mono ((pullbackAdjunction f).unit.app G) :=
    PhilipponEtaleStalkPullback.unit_mono_of_surjective f G
  let i : G ⟶ (pushforward f).obj (underlying.obj K) :=
    (pullbackAdjunction f).unit.app G ≫ (pushforward f).map a
  let : Mono ((pushforward f).map a) := Functor.map_mono (pushforward f) a
  let : Mono i := mono_comp ((pullbackAdjunction f).unit.app G) ((pushforward f).map a)
  let e := underlyingPushforwardIso f N K
  let k : G ⟶ U.obj ((modulePushforward f N).obj K) := i ≫ e.inv
  let : Mono k := mono_comp i e.inv
  let Uff : U.FullyFaithful :=
    fullyFaithfulSheafCompose X.smallEtaleTopology (forgetModuleFullyFaithful N)
  let iM : J ⟶ (modulePushforward f N).obj K := Uff.preimage k
  have hi : U.map iM = k := Uff.map_preimage k
  let : U.Faithful := Uff.faithful
  have hm : Mono (U.map iM) := by rw [hi]; exact inferInstanceAs (Mono k)
  let : Mono iM := Functor.mono_of_mono_map U hm
  let r := Injective.factorThru (𝟙 J) iM
  refine ⟨K, hK, i, e.inv ≫ U.map r, ?_⟩
  erw [← Category.assoc, show i ≫ e.inv = U.map iM from hi.symm, ← U.map_comp,
    Injective.comp_factorThru, U.map_id]

set_option maxHeartbeats 900000 in
/-- An injective module sheaf is a retract of a product of direct
images of injective module sheaves along a jointly surjective family. -/
theorem exists_directImage_product_retraction {I : Type u} {Y : I → Scheme.{u}}
    (g : ∀ i, Y i ⟶ X) (hCover : ∀ x : X, ∃ (i : I) (y : Y i), g i y = x) (N : ℕ)
    (J : Modules X N) [Injective J] :
    ∃ (K : ∀ i, Modules (Y i) N) (_ : ∀ i, Injective (K i))
      (P : Fan (fun i => (modulePushforward (g i) N).obj (K i)))
      (_ : Nonempty (IsLimit P)) (a : J ⟶ P.pt) (r : P.pt ⟶ J), a ≫ r = 𝟙 _ := by
  let U := underlying (X := X) (R := ULift.{u} (ZMod N))
  let Uf : U.FullyFaithful :=
    fullyFaithfulSheafCompose X.smallEtaleTopology (forgetModuleFullyFaithful N)
  let : U.Faithful := Uf.faithful
  have h (i : I) := exists_injective_module_embedding N
    ((pullbackSheaves (g i)).obj (U.obj J)) (pullback_underlying_killed (g i) N J)
  choose K hK b hb using h
  let D (i : I) := (modulePushforward (g i) N).obj (K i)
  let e (i : I) := underlyingPushforwardIso (g i) N (K i)
  let c (i : I) : U.obj J ⟶ (pushforward (g i)).obj (underlying.obj (K i)) :=
    (pullbackAdjunction (g i)).unit.app (U.obj J) ≫ (pushforward (g i)).map (b i)
  let a : J ⟶ ∏ᶜ D := Pi.lift fun i => Uf.preimage (c i ≫ (e i).inv)
  have hπ (i : I) : U.map a ≫ U.map (Pi.π D i) ≫ (e i).hom = c i := by
    rw [← Category.assoc, ← U.map_comp]
    dsimp only [a]
    rw [Pi.lift_π, Uf.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let t (j : Σ i : I, Y i) := PhilipponEtaleGeometricStalks.geometricMap j.2 ≫ g j.1
  have hRange : ⋃ j, Set.range (t j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := hCover x
    exact Set.mem_iUnion.mpr ⟨⟨i, y⟩, default, by simpa [t, Scheme.Hom.comp_apply] using hy⟩
  let P := ObjectProperty.ofObj fun j => Scheme.pointSmallEtale (t j)
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservative_pointSmallEtale t hRange
  let : ∀ Φ : P.FullSubcategory, Mono (Φ.obj.sheafFiber.map (U.map a)) := by
    intro Φ
    have hΦ := Φ.property
    change ObjectProperty.ofObj (fun j => Scheme.pointSmallEtale (t j)) Φ.obj at hΦ
    obtain ⟨j, hj⟩ := (ObjectProperty.ofObj_iff _ _).mp hΦ
    rw [← hj]
    let S := (Scheme.pointSmallEtale (t j)).sheafFiber (A := AddCommGrpCat.{u})
    let η := (pullbackAdjunction (g j.1)).unit.app (U.obj J)
    let : Mono (S.map η) :=
      (AddCommGrpCat.mono_iff_injective _).mpr
        (PhilipponEtaleStalkPullback.stalk_unit_injective (g j.1)
          (PhilipponEtaleGeometricStalks.geometricMap j.2) (U.obj J))
    let : Mono (b j.1) := hb j.1
    let : Mono ((pushforward (g j.1)).map (b j.1)) := Functor.map_mono _ _
    let : Mono (S.map (c j.1)) := by
      change Mono (S.map (η ≫ (pushforward (g j.1)).map (b j.1)))
      rw [S.map_comp]
      exact mono_comp _ _
    have hm : S.map (U.map a) ≫ S.map (U.map (Pi.π D j.1) ≫ (e j.1).hom) = S.map (c j.1) := by
      rw [← S.map_comp, hπ]
    exact mono_of_mono_fac hm
  let : Mono (U.map a) := (hP.jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono (U.map a)
  let : Mono a := Functor.mono_of_mono_map U inferInstance
  exact ⟨K, hK, Fan.mk _ (Pi.π D), ⟨productIsProduct D⟩,
    a, Injective.factorThru (𝟙 J) a, Injective.comp_factorThru _ _⟩

end PhilipponEtalePrimeTorsionComparison

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
namespace PhilipponEtaleAcyclicCohomology
universe u
private abbrev AbelianSheaves (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
/-- An exact direct image has no positive right derived functors. -/
theorem isZero_higherDirectImage_of_exact {X Y : Scheme.{u}} (f : Y ⟶ X)
    [PreservesFiniteColimits (pushforward f)] (F : AbelianSheaves Y) (q : ℕ) :
    IsZero (((pushforward f).rightDerived (q + 1)).obj F) := by
  let I := injectiveResolution F
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj (pushforward f) (q + 1))
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
  exact (show (I.cocomplex.sc (q + 1)).Exact from I.cocomplex_exactAt_succ q).map (pushforward f)

end PhilipponEtaleAcyclicCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward
  (pushforward fullyFaithfulPushforward isZero_stalk_pushforward_of_not_mem_range)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponEtalePullbackSquareUnits (pullbackSquareIsoOver)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback
  (exists_point_lift_of_mem_range stalk_unit_isIso stalkPullbackIso)


namespace PhilipponEtaleClosedImmersionBaseChange

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- A sheaf with zero stalks off a closed subscheme is recovered by
restricting to the closed subscheme and taking the direct image. -/
theorem isIso_unit_of_support {X Y : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    (F : Ab X)
    (hF : ∀ x : X, geometricMap x default ∉ Set.range f →
      IsZero ((geometricPoint x).sheafFiber.obj F)) :
    IsIso ((pullbackAdjunction f).unit.app F) := by
  let P := ObjectProperty.ofObj fun x : X => geometricPoint x
  have hP : P.IsConservativeFamilyOfPoints :=
    Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let η := (pullbackAdjunction f).unit.app F
  apply ((hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff η).mpr
  intro Φ
  have h := Φ.property
  change ObjectProperty.ofObj (fun x : X => geometricPoint x) Φ.obj at h
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp h
  rw [← hx]
  by_cases hs : geometricMap x default ∈ Set.range f
  · obtain ⟨t, ht⟩ := exists_point_lift_of_mem_range f (geometricMap x) hs
    change IsIso ((Scheme.pointSmallEtale (geometricMap x)).sheafFiber.map η)
    rw [← ht]
    exact stalk_unit_isIso f t F
  · exact (hF x hs).isIso
      (isZero_stalk_pushforward_of_not_mem_range f (geometricMap x) hs
        ((pullbackSheaves f).obj F)) _

/-- Direct image by a closed immersion commutes with arbitrary base
change on abelian étale sheaves. -/
def closedImmersionBaseChangeIso {X Y X' Y' : Scheme.{u}}
    {f : Y ⟶ X} [IsClosedImmersion f] {b : X' ⟶ X} {a : Y' ⟶ Y} {f' : Y' ⟶ X'}
    (h : IsPullback f' a b f) (F : Ab Y) :
    (pullbackSheaves b).obj ((pushforward f).obj F) ≅
      (pushforward f').obj ((pullbackSheaves a).obj F) := by
  let : IsClosedImmersion f' :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  let G := (pullbackSheaves b).obj ((pushforward f).obj F)
  have hrange : Set.range f' = b ⁻¹' Set.range f := by
    let e := h.isoPullback
    have he : Function.Surjective e.hom := e.hom.surjective
    calc
      Set.range f' = Set.range (pullback.fst b f ∘ e.hom) := by
        rw [← h.isoPullback_hom_fst]
        rfl
      _ = Set.range (pullback.fst b f) := he.range_comp _
      _ = _ := Scheme.Pullback.range_fst b f
  have hη : IsIso ((pullbackAdjunction f').unit.app G) := by
    apply isIso_unit_of_support f' G
    intro x hx
    have hs : (geometricMap x ≫ b) default ∉ Set.range f := by
      simpa only [hrange, Set.mem_preimage, Scheme.Hom.comp_apply] using hx
    have hz := isZero_stalk_pushforward_of_not_mem_range f (geometricMap x ≫ b) hs F
    exact hz.of_iso ((stalkPullbackIso b (geometricMap x)).app ((pushforward f).obj F))
  let ff := fullyFaithfulPushforward f
  let : (pushforward f).Full := ff.full
  let : (pushforward f).Faithful := ff.faithful
  let e := (pullbackSquareIsoOver b f f' a (f' ≫ b) rfl h.w.symm).app ((pushforward f).obj F)
  exact asIso ((pullbackAdjunction f').unit.app G) ≪≫
    (pushforward f').mapIso (e ≪≫ (pullbackSheaves a).mapIso (asIso ((pullbackAdjunction f).counit.app F)))

end PhilipponEtaleClosedImmersionBaseChange

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)


namespace PhilipponEtaleHigherImageComposition

universe u

theorem rightDerived_additive {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive] (q : ℕ) :
    (F.rightDerived q).Additive := by
  let : (injectiveResolutions C).Additive := by
    constructor
    intro X Y a b
    let I := injectiveResolution X
    let J := injectiveResolution Y
    let Q := HomotopyCategory.quotient C (ComplexShape.up ℕ)
    change Q.map (InjectiveResolution.desc (a + b) J I) =
      Q.map (InjectiveResolution.desc a J I) + Q.map (InjectiveResolution.desc b J I)
    rw [← Q.map_add]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descHomotopy (a + b) <;> simp
  dsimp only [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory]
  infer_instance

/-- When the coefficient is acyclic for the first direct image, the
higher direct images of the composite are those of its direct image. -/
def higherImageCompIso {X Y Z : Scheme.{u}} (f : Y ⟶ Z) (g : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (h : ∀ q : ℕ, IsZero (((pushforward g).rightDerived (q + 1)).obj F)) (n : ℕ) :
    ((pushforward (g ≫ f)).rightDerived n).obj F ≅
      ((pushforward f).rightDerived n).obj ((pushforward g).obj F) := by
  let I := injectiveResolution F
  let J := PhilipponDerivedAdjunction.mapInjectiveResolution (pushforward g) I h
  let e := Functor.mapHomologicalComplexCompIso (pushforwardCompIso f g) (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor
    (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℕ) n
  exact I.isoRightDerivedObj (pushforward (g ≫ f)) n ≪≫
    H.mapIso (e.symm.app I.cocomplex) ≪≫ (J.isoRightDerivedObj (pushforward f) n).symm

end PhilipponEtaleHigherImageComposition

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleHigherImageComposition (higherImageCompIso)
open PhilipponEtaleModuleSkyscrapers (underlying)
open PhilipponEtalePrimeTorsionComparison
  (modulePushforward underlyingPushforwardIso injective_modulePushforward exists_directImage_retraction
    exists_directImage_product_retraction)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleAcyclicBaseChange

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Coefficients (X : Scheme.{u}) (N : ℕ) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))

/-- Comparison of ordinary direct images in every pullback square. -/
def OrdinaryBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃X' Y' : Scheme.{u}⦄ ⦃a : X' ⟶ X⦄ ⦃b : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄,
    IsPullback f' a b f → ∀ F : Ab X,
    Nonempty ((pullbackSheaves b).obj ((pushforward f).obj F) ≅
      (pushforward f').obj ((pullbackSheaves a).obj F))

/-- Positive higher direct images vanish after every base change of an
injective coefficient sheaf. -/
def AcyclicInjectiveBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) : Prop :=
  ∀ ⦃X' Y' : Scheme.{u}⦄ ⦃a : X' ⟶ X⦄ ⦃b : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄,
    IsPullback f' a b f → ∀ J : Coefficients X N, Injective J → ∀ q : ℕ,
    IsZero (((pushforward f').rightDerived (q + 1)).obj
      ((pullbackSheaves a).obj (underlying.obj J)))

private theorem factorSquare {X Y Z X' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {a : X' ⟶ X} {c : Z' ⟶ Z} {k : X' ⟶ Z'} (h : IsPullback k a c (f ≫ g)) :
    ∃ f' : X' ⟶ pullback c g,
      IsPullback f' a (pullback.snd c g) f ∧ f' ≫ pullback.fst c g = k := by
  let right := IsPullback.of_hasPullback c g
  have hc : k ≫ c = (a ≫ f) ≫ g := by simpa only [Category.assoc] using h.w
  let f' := right.lift k (a ≫ f) hc
  have h₁ : f' ≫ pullback.fst c g = k := right.lift_fst _ _ _
  have h₂ : f' ≫ pullback.snd c g = a ≫ f := right.lift_snd _ _ _
  refine ⟨f', IsPullback.of_right ?_ h₂ right, h₁⟩
  rwa [h₁]

theorem OrdinaryBaseChange.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : OrdinaryBaseChange f) (hg : OrdinaryBaseChange g) : OrdinaryBaseChange (f ≫ g) := by
  intro X' Z' a c k h F
  obtain ⟨f', hLeft, hTop⟩ := factorSquare h
  subst k
  let g' := pullback.fst c g
  obtain ⟨eLeft⟩ := hf hLeft F
  obtain ⟨eRight⟩ := hg (IsPullback.of_hasPullback c g) ((pushforward f).obj F)
  exact ⟨(pullbackSheaves c).mapIso ((pushforwardCompIso g f).symm.app F) ≪≫
    eRight ≪≫ (pushforward g').mapIso eLeft ≪≫
      (pushforwardCompIso g' f').app ((pullbackSheaves a).obj F)⟩

theorem AcyclicInjectiveBaseChange.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {N : ℕ} (hf : AcyclicInjectiveBaseChange f N) (hg : AcyclicInjectiveBaseChange g N)
    (hf₀ : OrdinaryBaseChange f) : AcyclicInjectiveBaseChange (f ≫ g) N := by
  intro X' Z' a c k h J hJ q
  obtain ⟨f', hLeft, hTop⟩ := factorSquare h
  subst k
  let g' := pullback.fst c g
  let b := pullback.snd c g
  let F := (pullbackSheaves a).obj (underlying.obj J)
  let K := (modulePushforward f N).obj J
  let : Injective J := hJ
  obtain ⟨eLeft⟩ := hf₀ hLeft (underlying.obj J)
  let e : (pushforward f').obj F ≅ (pullbackSheaves b).obj (underlying.obj K) :=
    eLeft.symm ≪≫ (pullbackSheaves b).mapIso (underlyingPushforwardIso f N J).symm
  let eHigher := higherImageCompIso g' f' F (hf hLeft J hJ) (q + 1) ≪≫
    ((pushforward g').rightDerived (q + 1)).mapIso e
  exact (hg (IsPullback.of_hasPullback c g) K (injective_modulePushforward f N J) q).of_iso eHigher

set_option maxHeartbeats 650000 in
/-- Positive-degree base change descends across a surjective cover if
ordinary and positive-degree base change hold along the cover. -/
theorem AcyclicInjectiveBaseChange.of_surjective_comp {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} [Surjective f] {N : ℕ}
    (hf : AcyclicInjectiveBaseChange f N) (hcomp : AcyclicInjectiveBaseChange (f ≫ g) N)
    (hf₀ : OrdinaryBaseChange f) : AcyclicInjectiveBaseChange g N := by
  intro Y' Z' b c g' hRight J hJ q
  let f' := pullback.fst b f
  let a := pullback.snd b f
  let hLeft := IsPullback.of_hasPullback b f
  let : Injective J := hJ
  obtain ⟨K, hK, i, r, hir⟩ := exists_directImage_retraction f N J
  obtain ⟨eLeft⟩ := hf₀ hLeft (underlying.obj K)
  let H := (pushforward g').rightDerived (q + 1)
  let T := pullbackSheaves b ⋙ H
  let F := (pullbackSheaves a).obj (underlying.obj K)
  let e := H.mapIso eLeft ≪≫ (higherImageCompIso g' f' F (hf hLeft K hK) (q + 1)).symm
  have hz : IsZero (T.obj ((pushforward f).obj (underlying.obj K))) :=
    (hcomp (hLeft.paste_horiz hRight) K hK q).of_iso e
  have hSplit : T.map i ≫ T.map r = 𝟙 (T.obj (underlying.obj J)) := by
    rw [← T.map_comp, hir, T.map_id]
  let : Mono (T.map i) := mono_of_mono_fac hSplit
  exact IsZero.of_mono (T.map i) hz

set_option maxHeartbeats 750000 in
/-- A finite jointly surjective family suffices for cancellation of
positive-degree base change by taking a finite product of direct images. -/
theorem AcyclicInjectiveBaseChange.of_jointlySurjective_comp {X S : Scheme.{u}}
    {I : Type u} [Finite I] {Y : I → Scheme.{u}} (p : ∀ i, Y i ⟶ X) {f : X ⟶ S} {N : ℕ}
    (cover : ∀ x : X, ∃ (i : I) (y : Y i), p i y = x)
    (hp : ∀ i, AcyclicInjectiveBaseChange (p i) N)
    (hpf : ∀ i, AcyclicInjectiveBaseChange (p i ≫ f) N)
    (hp₀ : ∀ i, OrdinaryBaseChange (p i)) : AcyclicInjectiveBaseChange f N := by
  intro X' S' b c f' hRight J hJ q
  let : Injective J := hJ
  obtain ⟨K, hK, P, ⟨hP⟩, a, r, har⟩ := exists_directImage_product_retraction p cover N J
  let D (i : I) := (modulePushforward (p i) N).obj (K i)
  let U : Coefficients X N ⥤ Ab X := underlying
  let H : Ab X' ⥤ Ab S' := (pushforward f').rightDerived (q + 1)
  let T : Coefficients X N ⥤ Ab S' := U ⋙ pullbackSheaves b ⋙ H
  let : U.Additive := ⟨fun {_ _} _ _ => rfl⟩
  let : (pullbackSheaves b).Additive := (pullbackAdjunction b).left_adjoint_additive
  let : H.Additive := PhilipponEtaleHigherImageComposition.rightDerived_additive (pushforward f') (q + 1)
  let : T.Additive := inferInstanceAs (U ⋙ pullbackSheaves b ⋙ H).Additive
  let : PreservesFiniteProducts T := Functor.preservesFiniteProductsOfAdditive T
  have hz (i : I) : IsZero (T.obj (D i)) := by
    let p' := pullback.fst b (p i)
    let k := pullback.snd b (p i)
    let hLeft := IsPullback.of_hasPullback b (p i)
    let F := (pullbackSheaves k).obj (underlying.obj (K i))
    obtain ⟨eLeft⟩ := hp₀ i hLeft (underlying.obj (K i))
    let e := (pullbackSheaves b).mapIso (underlyingPushforwardIso (p i) N (K i)) ≪≫ eLeft
    exact (hpf i (hLeft.paste_horiz hRight) (K i) (hK i) q).of_iso
      (H.mapIso e ≪≫ (higherImageCompIso f' p' F (hp i hLeft (K i) (hK i)) (q + 1)).symm)
  let c := T.mapCone P
  have hc : IsLimit c := isLimitOfPreserves T hP
  have hProd : IsZero c.pt := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply hc.hom_ext
    intro j
    exact (hz j.as).eq_of_tgt _ _
  have hSplit : T.map a ≫ T.map r = 𝟙 (T.obj J) := by rw [← T.map_comp, har, T.map_id]
  let : Mono (T.map a) := mono_of_mono_fac hSplit
  exact IsZero.of_mono (T.map a) hProd

theorem ordinaryBaseChange_closedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : OrdinaryBaseChange f := by
  intro X' Y' a b f' h F
  exact ⟨PhilipponEtaleClosedImmersionBaseChange.closedImmersionBaseChangeIso h F⟩

theorem acyclicInjectiveBaseChange_closedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (N : ℕ) : AcyclicInjectiveBaseChange f N := by
  intro X' Y' a b f' h J _ q
  let : IsClosedImmersion f' :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip inferInstance
  let : PreservesFiniteColimits (pushforward f') :=
    AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite f'
  exact PhilipponEtaleAcyclicCohomology.isZero_higherDirectImage_of_exact f'
    ((pullbackSheaves a).obj (underlying.obj J)) q

/-- A cover that embeds into a proper ambient scheme inherits base
change from the projections over the base and over the target of the cover. -/
theorem projectiveCover_baseChange {X Y P S : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] (p : Y ⟶ X)
    (r : P ⟶ S) [IsProper r] (i : Y ⟶ P) [IsClosedImmersion i]
    (hi : i ≫ r = p ≫ f) {N : ℕ}
    (hr : AcyclicInjectiveBaseChange r N)
    (hproj : AcyclicInjectiveBaseChange (pullback.fst f r) N)
    (hproj₀ : OrdinaryBaseChange (pullback.fst f r)) :
    AcyclicInjectiveBaseChange p N ∧
      AcyclicInjectiveBaseChange (p ≫ f) N ∧ OrdinaryBaseChange p := by
  let k := pullback.lift p i hi.symm
  have hs : k ≫ pullback.snd f r = i := pullback.lift_snd _ _ _
  have hk : k ≫ pullback.fst f r = p := pullback.lift_fst _ _ _
  let : IsImmersion (k ≫ pullback.snd f r) := hs ▸ inferInstanceAs (IsImmersion i)
  let : IsImmersion k := IsImmersion.of_comp k (pullback.snd f r)
  let q := pullback.snd f r ≫ r
  let : IsSeparated q := inferInstanceAs (IsSeparated (pullback.snd f r ≫ r))
  let : IsProper (k ≫ q) := by
    change IsProper (k ≫ pullback.snd f r ≫ r)
    rw [← Category.assoc, hs]
    infer_instance
  let : IsProper k := IsProper.of_comp k q
  let : IsClosedImmersion k := IsClosedImmersion.of_isPreimmersion k k.isClosedMap.isClosed_range
  have hp := (acyclicInjectiveBaseChange_closedImmersion k N).comp hproj
    (ordinaryBaseChange_closedImmersion k)
  have hp₀ := (ordinaryBaseChange_closedImmersion k).comp hproj₀
  have hpf := (acyclicInjectiveBaseChange_closedImmersion i N).comp hr
    (ordinaryBaseChange_closedImmersion i)
  rw [hk] at hp hp₀
  rw [hi] at hpf
  exact ⟨hp, hpf, hp₀⟩

/-- A surjective cover that embeds into a proper ambient scheme reduces
acyclicity to the ambient projection and its pullback to the target. -/
theorem acyclicInjectiveBaseChange_of_projectiveCover {X Y P S : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] (p : Y ⟶ X) [Surjective p]
    (r : P ⟶ S) [IsProper r] (i : Y ⟶ P) [IsClosedImmersion i]
    (hi : i ≫ r = p ≫ f) {N : ℕ}
    (hr : AcyclicInjectiveBaseChange r N)
    (hproj : AcyclicInjectiveBaseChange (pullback.fst f r) N)
    (hproj₀ : OrdinaryBaseChange (pullback.fst f r)) : AcyclicInjectiveBaseChange f N := by
  obtain ⟨hp, hpf, hp₀⟩ := projectiveCover_baseChange f p r i hi hr hproj hproj₀
  exact hp.of_surjective_comp hpf hp₀

end PhilipponEtaleAcyclicBaseChange

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open PhilipponEtaleAcyclicBaseChange


namespace PhilipponEtaleProjectiveZero

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

private abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 1) R
private abbrev coordinate : MvPolynomial (Fin 1) R := MvPolynomial.X 0
private abbrev chartRing := Away (grading R) (coordinate R)

private theorem chartRing_surjective : Function.Surjective (algebraMap R (chartRing R)) := by
  let C := Algebra.ofId R (chartRing R)
  apply (AlgHom.range_eq_top C).mp
  apply le_antisymm le_top
  rw [← ProjSpace.adjoin_range_ratio R 0 0]
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  let : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  rw [Subsingleton.elim i 0, ProjSpace.ratio_self]
  exact C.range.one_mem

private theorem chartRing_injective : Function.Injective (algebraMap R (chartRing R)) := by
  let ev := MvPolynomial.eval (fun _ : Fin 1 => (1 : R))
  have ht : IsUnit (ev (coordinate R)) := by simp [ev]
  let lift := Localization.awayLift ev (coordinate R) ht
  let r := lift.comp (algebraMap (chartRing R) (Localization.Away (coordinate R)))
  apply Function.LeftInverse.injective (g := r)
  intro a
  change lift ((algebraMap R (chartRing R) a).val) = a
  rw [ProjSpace.val_algebraMap]
  simp only [lift, Localization.awayLift, IsLocalization.Away.lift_eq, ev, MvPolynomial.eval_C]

/-- The projection of projective zero-space is an isomorphism over every
commutative ring. -/
theorem isIso_projection : IsIso (ProjSpace.π R 0) := by
  let e := Proj.awayι (grading R) (coordinate R) (ProjSpace.X_mem_one R 0 0) one_pos
  have hcover : ⨆ i : Fin 1, Proj.basicOpen (grading R) (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top (grading R) _ (ProjSpace.irrelevant_le_span_X R 0)
  have htop : Proj.basicOpen (grading R) (coordinate R) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hcover]
    exact iSup_le fun i => by rw [Subsingleton.elim i 0]
  let : Surjective e := by
    constructor
    rw [← Set.range_eq_univ, ← Scheme.Hom.coe_opensRange]
    change (e.opensRange : Set (Proj (grading R))) = Set.univ
    rw [show e.opensRange = _ from Proj.opensRange_awayι _ _ _ _, htop]
    rfl
  let : IsOpenImmersion e := inferInstanceAs (IsOpenImmersion (Proj.awayι ..))
  let : IsIso e := (isIso_iff_isOpenImmersion_and_surjective e).mpr ⟨inferInstance, inferInstance⟩
  rw [← isIso_comp_left_iff e]
  let C := CommRingCat.ofHom (algebraMap R (chartRing R))
  let : IsIso C := (ConcreteCategory.isIso_iff_bijective C).mpr
    ⟨chartRing_injective R, chartRing_surjective R⟩
  change IsIso (Proj.awayι (grading R) (coordinate R) (ProjSpace.X_mem_one R 0 0) one_pos ≫
    ProjSpace.π R 0)
  rw [ProjSpace.awayι_comp_π]
  exact inferInstanceAs (IsIso (Spec.map C))

/-- Ordinary base change and higher-image vanishing both hold for any
pullback of the projective zero-space projection. -/
theorem baseChange_of_zero_projection {P S : Scheme.{u}} (v : S ⟶ Spec (.of R))
    (a : P ⟶ Proj (grading R)) (r : P ⟶ S) (h : IsPullback a r (ProjSpace.π R 0) v)
    (N : ℕ) : OrdinaryBaseChange r ∧ AcyclicInjectiveBaseChange r N := by
  let : IsIso r := h.isIso_snd_of_isIso (isIso_projection R)
  exact ⟨ordinaryBaseChange_closedImmersion r, acyclicInjectiveBaseChange_closedImmersion r N⟩

end PhilipponEtaleProjectiveZero

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (isZero_higherDirectImage_of_exact)
open PhilipponEtaleAcyclicBaseChange (AcyclicInjectiveBaseChange OrdinaryBaseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleModuleSkyscrapers (underlying)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleProjectiveLineTower

universe u

private theorem exists_relativeLine_pullback {R : Type u} [CommRing R] {S T : Scheme.{u}}
    (v : S ⟶ Spec (.of R)) (w : T ⟶ S) :
    ∃ c : pullback (w ≫ v) (ProjSpace.π R 1) ⟶ pullback v (ProjSpace.π R 1),
      IsPullback (pullback.fst (w ≫ v) (ProjSpace.π R 1)) c w
        (pullback.fst v (ProjSpace.π R 1)) := by
  let f := ProjSpace.π R 1
  let e := (pullbackRightPullbackFstIso v f w).symm
  let c := e.hom ≫ pullback.snd w (pullback.fst v f)
  have hFst : e.hom ≫ pullback.fst w (pullback.fst v f) = pullback.fst (w ≫ v) f :=
    pullbackRightPullbackFstIso_inv_fst v f w
  refine ⟨c, IsPullback.of_iso_pullback ⟨?_⟩ e hFst rfl⟩
  rw [← hFst, Category.assoc, pullback.condition, ← Category.assoc]

/-- The projective-line tower commutes with base change. -/
theorem exists_linePower_pullback {R : Type u} [CommRing R] {S T : Scheme.{u}}
    (v : S ⟶ Spec (.of R)) (w : T ⟶ S) (n : ℕ) :
    ∃ c : (linePower (w ≫ v) n).left ⟶ (linePower v n).left,
      IsPullback (linePower (w ≫ v) n).hom c w (linePower v n).hom := by
  induction n with
  | zero => exact exists_relativeLine_pullback v w
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      let d := (linePower (w ≫ v) n).hom
      let e := (linePower v n).hom
      have h : d ≫ (w ≫ v) = c ≫ e ≫ v := by
        rw [← Category.assoc, hc.w, Category.assoc]
      have hNext :
          ∃ k : pullback (d ≫ (w ≫ v)) (ProjSpace.π R 1) ⟶ pullback (e ≫ v) (ProjSpace.π R 1),
            IsPullback (pullback.fst (d ≫ (w ≫ v)) (ProjSpace.π R 1)) k c
              (pullback.fst (e ≫ v) (ProjSpace.π R 1)) := by
        rw [h]
        exact exists_relativeLine_pullback (e ≫ v) c
      obtain ⟨k, hk⟩ := hNext
      exact ⟨k, hk.paste_horiz hc⟩

/-- A finite surjection from a projective-line tower over the affine base
gives a finite surjection from the same tower after any base change. -/
theorem exists_finite_linePower_cover_pullback {R : Type u} [CommRing R] {X P S : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (v : S ⟶ Spec (.of R)) (r : P ⟶ S) (a : P ⟶ X)
    (h : IsPullback a r f v) (n : ℕ)
    (k : (linePower (𝟙 (Spec (.of R))) n).left ⟶ X) [IsFinite k] [Surjective k]
    (hk : k ≫ f = (linePower (𝟙 (Spec (.of R))) n).hom) :
    ∃ l : (linePower v n).left ⟶ P, IsFinite l ∧ Surjective l ∧ l ≫ r = (linePower v n).hom := by
  obtain ⟨c, hc⟩ : ∃ c : (linePower v n).left ⟶ (linePower (𝟙 (Spec (.of R))) n).left,
      IsPullback (linePower v n).hom c v (linePower (𝟙 (Spec (.of R))) n).hom := by
    let assertion (u : S ⟶ Spec (.of R)) :=
      ∃ c : (linePower u n).left ⟶ (linePower (𝟙 (Spec (.of R))) n).left,
        IsPullback (linePower u n).hom c v (linePower (𝟙 (Spec (.of R))) n).hom
    exact Eq.mp (congrArg assertion (Category.comp_id v))
      (exists_linePower_pullback (𝟙 (Spec (.of R))) v n)
  let b := (linePower v n).hom
  have hComm : (c ≫ k) ≫ f = b ≫ v := by
    rw [Category.assoc, hk]
    exact hc.w.symm
  let l := h.lift (c ≫ k) b hComm
  have h₁ : l ≫ a = c ≫ k := h.lift_fst _ _ _
  have h₂ : l ≫ r = b := h.lift_snd _ _ _
  have hOuter : IsPullback (l ≫ r) c v (k ≫ f) := by
    rw [h₂, hk]
    exact hc
  have hLeft : IsPullback l c a k := IsPullback.of_right hOuter h₁ h.flip
  exact ⟨l, MorphismProperty.of_isPullback hLeft.flip (inferInstance : IsFinite k),
    MorphismProperty.of_isPullback hLeft.flip (inferInstance : Surjective k), h₂⟩

/-- Base-change vanishing for a relative projective line propagates
to every positive power by composition. -/
theorem acyclicInjectiveBaseChange_linePower {R : Type u} [CommRing R] {S : Scheme.{u}}
    (v : S ⟶ Spec (.of R)) (N : ℕ)
    (hOrd : ∀ {T : Scheme.{u}} (w : T ⟶ Spec (.of R)),
      OrdinaryBaseChange (pullback.fst w (ProjSpace.π R 1)))
    (hAcyc : ∀ {T : Scheme.{u}} (w : T ⟶ Spec (.of R)),
      AcyclicInjectiveBaseChange (pullback.fst w (ProjSpace.π R 1)) N)
    (n : ℕ) : AcyclicInjectiveBaseChange (linePower v n).hom N := by
  induction n with
  | zero => exact hAcyc v
  | succ n ih =>
      let w := (linePower v n).hom ≫ v
      exact AcyclicInjectiveBaseChange.comp (hAcyc w) ih (hOrd w)

/-- A finite surjection from a relative power of projective lines transfers
positive-degree base change to the covered morphism. -/
theorem acyclicInjectiveBaseChange_of_finite_linePower_cover {R : Type u} [CommRing R]
    {P S : Scheme.{u}} (v : S ⟶ Spec (.of R)) (r : P ⟶ S) (N n : ℕ)
    (k : (linePower v n).left ⟶ P) [IsFinite k] [Surjective k]
    (hk : k ≫ r = (linePower v n).hom)
    (hFiniteExact : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsFinite f → PreservesFiniteColimits (pushforward f))
    (hFiniteOrd : OrdinaryBaseChange k)
    (hOrd : ∀ {T : Scheme.{u}} (w : T ⟶ Spec (.of R)),
      OrdinaryBaseChange (pullback.fst w (ProjSpace.π R 1)))
    (hAcyc : ∀ {T : Scheme.{u}} (w : T ⟶ Spec (.of R)),
      AcyclicInjectiveBaseChange (pullback.fst w (ProjSpace.π R 1)) N) :
    AcyclicInjectiveBaseChange r N := by
  have hVanishing : AcyclicInjectiveBaseChange k N := by
    intro X' Y' a b f' h J _ q
    have : IsFinite f' := MorphismProperty.of_isPullback h.flip (inferInstance : IsFinite k)
    let : PreservesFiniteColimits (pushforward f') := hFiniteExact f' inferInstance
    exact isZero_higherDirectImage_of_exact f' ((pullbackSheaves a).obj (underlying.obj J)) q
  apply AcyclicInjectiveBaseChange.of_surjective_comp hVanishing _ hFiniteOrd
  rw [hk]
  exact acyclicInjectiveBaseChange_linePower v N hOrd hAcyc n

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Positive-degree base change for projective projections follows from
the projective line and the finite surjections from its powers. -/
theorem acyclicInjectiveBaseChange_projective_of_line_and_covers
    (R : Type u) [CommRing R] (N : ℕ)
    (hProperOrd : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsProper f → OrdinaryBaseChange f)
    (hFiniteExact : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsFinite f → PreservesFiniteColimits (pushforward f))
    (hLine : ∀ {S : Scheme.{u}} (v : S ⟶ Spec (.of R)),
      AcyclicInjectiveBaseChange (pullback.fst v (ProjSpace.π R 1)) N)
    (hCover : ∀ n : ℕ, ∃ k : (linePower (𝟙 (Spec (.of R))) n).left ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1 + 1)) R),
      IsFinite k ∧ Surjective k ∧ k ≫ ProjSpace.π R (n + 1) = (linePower (𝟙 (Spec (.of R))) n).hom)
    (n : ℕ) {P S : Scheme.{u}} (v : S ⟶ Spec (.of R)) (r : P ⟶ S)
    (a : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    (h : IsPullback a r (ProjSpace.π R n) v) : AcyclicInjectiveBaseChange r N := by
  cases n with
  | zero => exact (PhilipponEtaleProjectiveZero.baseChange_of_zero_projection R v a r h N).2
  | succ n =>
      obtain ⟨k, hk, hs, hComp⟩ := hCover n
      obtain ⟨l, hFin, hSurj, hComp'⟩ :=
        exists_finite_linePower_cover_pullback (ProjSpace.π R (n + 1)) v r a h n k hComp
      exact acyclicInjectiveBaseChange_of_finite_linePower_cover v r N n l hComp' hFiniteExact
        (hProperOrd l inferInstance) (fun w => hProperOrd _ inferInstance) hLine

end PhilipponEtaleProjectiveLineTower

end

open CategoryTheory.Abelian
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (R : Type u) [CommRing R] (n : ℕ) {P S : Scheme.{u}}
    (v : S ⟶ Spec (.of R))
    (a : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (r : P ⟶ S)
    (h : IsPullback a r (ProjSpace.π R n) v)
    {P' S' : Scheme.{u}} (c : P' ⟶ P) (b : S' ⟶ S) (r' : P' ⟶ S')
    (h' : IsPullback r' c b r)
    (N : ℕ) (hN : N.Prime)
    (J : Sheaf P.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (hJ : Injective J)
    (G : Sheaf P.smallEtaleTopology AddCommGrpCat.{u})
    (hG : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (q : ℕ) :
    IsZero (((PhilipponEtaleClosedPushforward.pushforward r').rightDerived (q + 1)).obj ((PhilipponEtaleSmallSite.pullbackSheaves c).obj G)) := by
  let U := PhilipponEtaleModuleSkyscrapers.underlying (X := P)
    (R := ULift.{u} (ZMod N))
  have hUnderlying : G = U.obj J := ObjectProperty.FullSubcategory.ext hG
  rw [hUnderlying]
  refine PhilipponEtaleProjectiveLineTower.acyclicInjectiveBaseChange_projective_of_line_and_covers
    R N ?_ ?_ ?_ (AlgebraicGeometry.Scheme.exists_finite_surjective_projectiveLinePower_cover R) n v r a h h' J hJ q
  · intro X Y f hf X' Y' a b f' hF F
    exact AlgebraicGeometry.Scheme.nonempty_etale_directImage_baseChange_of_isProper f a b f' hF F
  · intro X Y f hf
    exact AlgebraicGeometry.Scheme.etale_pushforward_preservesFiniteColimits_of_isFinite f
  · intro S w P' S' c b r' hW K hK d
    exact AlgebraicGeometry.Scheme.isZero_etale_higherDirectImage_of_prime_injective_projectiveLine_base_change R w c b r' hW N hN K hK
      (PhilipponEtaleModuleSkyscrapers.underlying.obj K) rfl d


end
