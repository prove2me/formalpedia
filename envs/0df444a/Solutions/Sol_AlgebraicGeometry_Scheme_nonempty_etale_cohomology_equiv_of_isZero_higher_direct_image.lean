-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_cohomology_equiv_of_isZero_higher_direct_image
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T20:22:38.214543+00:00
-- url     : https://prove2.me/submissions/8c2ef719-bcf6-433c-be9c-29c163e4eea7

import Definitions.Def_AlgebraicGeometry_SmallEtaleAbelianDirectImage
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.Pullback

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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteLimitSubsite

universe w v v' u u'

private def Shape : Bool → Type
  | false => Discrete PEmpty.{1}
  | true => WalkingCospan

private instance (b : Bool) : Small.{w} (Shape b) := by
  cases b <;> dsimp [Shape] <;> infer_instance

private instance (b : Bool) : Category.{0} (Shape b) := by
  cases b <;> dsimp [Shape] <;> infer_instance

private instance (b : Bool) : LocallySmall.{w} (Shape b) := by
  cases b <;> dsimp [Shape] <;> infer_instance

variable {C : Type u} [Category.{v} C]

/-- Closure of a collection of objects under isomorphisms, a terminal
object and pullbacks. -/
def closure (P : ObjectProperty C) : ObjectProperty C :=
  P.limitsClosure Shape

theorem le_closure (P : ObjectProperty C) : P ≤ closure P := P.le_limitsClosure Shape

instance (P : ObjectProperty C) [LocallySmall.{w} C] [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} (closure P) :=
  inferInstanceAs (ObjectProperty.EssentiallySmall.{w} (P.limitsClosure Shape))

private instance (P : ObjectProperty C) :
    (closure P).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) :=
  P.instIsClosedUnderLimitsOfShapeLimitsClosure Shape false

private instance (P : ObjectProperty C) :
    (closure P).IsClosedUnderLimitsOfShape WalkingCospan :=
  P.instIsClosedUnderLimitsOfShapeLimitsClosure Shape true

instance (P : ObjectProperty C) [HasTerminal C] :
    HasTerminal (closure P).FullSubcategory := by infer_instance

instance (P : ObjectProperty C) [HasPullbacks C] :
    HasPullbacks (closure P).FullSubcategory := by infer_instance

instance (P : ObjectProperty C) [HasFiniteLimits C] :
    HasFiniteLimits (closure P).FullSubcategory :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

instance (P : ObjectProperty C) [HasFiniteLimits C] :
    PreservesFiniteLimits (closure P).ι :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

variable {D : Type u'} [Category.{v'} D]

theorem closure_maps {P : ObjectProperty C} {Q : ObjectProperty D} (F : C ⥤ D)
    [PreservesFiniteLimits F] (h : P ≤ Q.inverseImage F) :
    closure P ≤ (closure Q).inverseImage F := by
  have (b : Bool) : ((closure Q).inverseImage F).IsClosedUnderLimitsOfShape (Shape b) := by
    cases b <;> dsimp only [Shape] <;> infer_instance
  letI : (closure Q).IsClosedUnderIsomorphisms :=
    inferInstanceAs ((Q.limitsClosure Shape).IsClosedUnderIsomorphisms)
  exact ObjectProperty.limitsClosure_le (h.trans (fun _ hq => le_closure Q _ hq))

/-- A finite-limit-preserving functor acts on the small closure if it maps
the chosen generating objects into the target generating collection. -/
def restrict {P : ObjectProperty C} {Q : ObjectProperty D} (F : C ⥤ D)
    [PreservesFiniteLimits F] (h : P ≤ Q.inverseImage F) :
    (closure P).FullSubcategory ⥤ (closure Q).FullSubcategory :=
  (closure Q).lift ((closure P).ι ⋙ F) (fun U => closure_maps F h _ U.property)

instance {P : ObjectProperty C} {Q : ObjectProperty D} [HasFiniteLimits C] [HasFiniteLimits D]
    (F : C ⥤ D) [PreservesFiniteLimits F] (h : P ≤ Q.inverseImage F) :
    PreservesFiniteLimits (restrict F h) := by
  have : PreservesFiniteLimits (restrict F h ⋙ (closure Q).ι) :=
    show PreservesFiniteLimits ((closure P).ι ⋙ F) from comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (closure Q).ι

end PhilipponFiniteLimitSubsite

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponFiniteLimitSubsite
open PhilipponEtaleBaseChangeComparison (baseChange)


namespace PhilipponEtaleSmallSite

universe u
variable (X : Scheme.{u})

private def affineObjects : ObjectProperty X.Etale := fun U => IsAffine U.left

private theorem affine_in_image (U : X.Etale) (h : affineObjects X U) :
    (Scheme.AffineEtale.Spec X).essImage U := by
  let : IsAffine U.left := h
  let e := U.left.isoSpec
  let T := Scheme.AffineEtale.mk (e.inv ≫ U.hom)
  exact ⟨T, ⟨MorphismProperty.Over.isoMk e.symm rfl⟩⟩

private instance : ObjectProperty.EssentiallySmall.{u} (affineObjects X) :=
  ObjectProperty.EssentiallySmall.of_le (affine_in_image X)

private structure Generators (X : Scheme.{u}) where
  property : ObjectProperty X.Etale
  small : ObjectProperty.EssentiallySmall.{u} property
  containsAffine : affineObjects X ≤ property

attribute [instance] Generators.small

private def domainGenerators : Generators X :=
  ⟨affineObjects X, inferInstance, le_rfl⟩

variable {X} (G : Generators X)

private abbrev objects := closure G.property

/-- A universe-`u` model of a full dense subsite of the small étale site.
The subsite contains all affine étale objects and is closed under finite limits. -/
private def ModelSite : Type u := SmallModel.{u} (objects G).FullSubcategory

instance : SmallCategory (ModelSite G) :=
  inferInstanceAs (SmallCategory (SmallModel.{u} (objects G).FullSubcategory))

private def model : (objects G).FullSubcategory ≌ ModelSite G :=
  equivSmallModel.{u} (objects G).FullSubcategory

private instance : HasFiniteLimits (ModelSite G) where
  out _ _ _ := Adjunction.hasLimitsOfShape_of_equivalence (model G).inverse

private abbrev incl : ModelSite G ⥤ X.Etale := (model G).inverse ⋙ (objects G).ι

private theorem has_cover (V : X.Etale) :
    ∃ (I : Type u) (U : I → ModelSite G) (g : ∀ j, (incl G).obj (U j) ⟶ V),
      Sieve.ofArrows (fun j => (incl G).obj (U j)) g ∈ X.smallEtaleTopology V := by
  let A := V.left.affineCover
  let W (j : A.I₀) := Scheme.Etale.mk (A.f j ≫ V.hom)
  let B (j : A.I₀) : (objects G).FullSubcategory :=
    ⟨W j, le_closure _ _ (G.containsAffine _ (inferInstanceAs (IsAffine (A.X j))))⟩
  let U (j : A.I₀) := (model G).functor.obj (B j)
  let e (j : A.I₀) := (objects G).ι.mapIso ((model G).unitIso.app (B j)).symm
  let h (j : A.I₀) : W j ⟶ V := MorphismProperty.Over.homMk (A.f j) rfl trivial
  let g (j : A.I₀) : (incl G).obj (U j) ⟶ V := (e j).hom ≫ h j
  refine ⟨A.I₀, U, g, (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  obtain ⟨j, y, rfl⟩ := A.exists_eq x
  let E := (Scheme.Etale.forget X ⋙ Over.forget X).mapIso (e j)
  obtain ⟨z, hz⟩ := E.hom.homeomorph.surjective y
  exact Set.mem_iUnion.mpr ⟨j, ⟨z, congrArg (A.f j) hz⟩⟩

private instance : (incl G).IsCoverDense X.smallEtaleTopology where
  is_cover V := by
    obtain ⟨I, U, g, hg⟩ := has_cover G V
    refine X.smallEtaleTopology.superset_covering ?_ hg
    rintro W _ ⟨T, a, _, ⟨j⟩, rfl⟩
    exact (Sieve.coverByImage (incl G) V).downward_closed
      (Presieve.in_coverByImage (incl G) (g j)) a

private def topology : GrothendieckTopology (ModelSite G) :=
  (incl G).inducedTopology X.smallEtaleTopology

private theorem sheafify_small {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u} := by infer_instance

private instance (priority := 2000) : HasSheafify (topology G) AddCommGrpCat.{u} :=
  sheafify_small (topology G)

private instance : (incl G).IsDenseSubsite (topology G) X.smallEtaleTopology :=
  inferInstanceAs ((incl G).IsDenseSubsite
    ((incl G).inducedTopology X.smallEtaleTopology) X.smallEtaleTopology)

private instance : (incl G).IsOneHypercoverDense.{u} (topology G) X.smallEtaleTopology :=
  Functor.IsOneHypercoverDense.of_hasPullbacks (has_cover G)

private abbrev abelianSheaves := Sheaf (topology G) AddCommGrpCat.{u}

private abbrev bigSheaves (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private def restrictSheaves : bigSheaves X ⥤ abelianSheaves G :=
  (incl G).sheafPushforwardContinuous _ _ _

private instance : (restrictSheaves G).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense (incl G) (topology G)
    X.smallEtaleTopology AddCommGrpCat.{u}

/-- The small site generated under finite limits by the affine étale objects. -/
abbrev Site (X : Scheme.{u}) : Type u := ModelSite (domainGenerators X)

variable {Z : Scheme.{u}} (i : Z ⟶ X)

private instance finiteLimits_baseChange : PreservesFiniteLimits (baseChange i) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ i))

private instance finiteLimits_etale (Y : Scheme.{u}) : HasFiniteLimits Y.Etale :=
  inferInstanceAs (HasFiniteLimits (MorphismProperty.Over (@Etale) ⊤ Y))

private def targetGenerators : Generators Z where
  property := affineObjects Z ⊔ (affineObjects X).map (baseChange i)
  small := inferInstance
  containsAffine := le_sup_left

private theorem affine_baseChange :
    (domainGenerators X).property ≤ (targetGenerators i).property.inverseImage (baseChange i) := by
  intro U hU
  exact Or.inr ((affineObjects X).prop_map_obj (baseChange i) hU)

private def restrictBaseChange :
    (objects (domainGenerators X)).FullSubcategory ⥤ (objects (targetGenerators i)).FullSubcategory :=
  restrict (baseChange i) (affine_baseChange i)

private instance : PreservesFiniteLimits (restrictBaseChange i) :=
  inferInstanceAs (PreservesFiniteLimits (restrict (baseChange i) (affine_baseChange i)))

private def smallBaseChange : ModelSite (domainGenerators X) ⥤ ModelSite (targetGenerators i) :=
  (model (domainGenerators X)).inverse ⋙ restrictBaseChange i ⋙ (model (targetGenerators i)).functor

private instance : PreservesFiniteLimits (smallBaseChange i) := by
  have : PreservesFiniteLimits (restrictBaseChange i ⋙ (model (targetGenerators i)).functor) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

private def changeInclIso : smallBaseChange i ⋙ incl (targetGenerators i) ≅ incl (domainGenerators X) ⋙ baseChange i :=
  NatIso.ofComponents
    (fun U => (objects (targetGenerators i)).ι.mapIso
      ((model (targetGenerators i)).unitIso.app ((restrictBaseChange i).obj ((model (domainGenerators X)).inverse.obj U))).symm)
    (fun g => by
      simp only [Functor.comp_map, Functor.mapIso_hom, Iso.symm_hom, ← Functor.map_comp]
      apply congrArg
      exact (model (targetGenerators i)).unitIso.inv.naturality ((restrictBaseChange i).map ((model (domainGenerators X)).inverse.map g)))

private theorem coverPreserving_of_iso {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} (e : F ≅ G) (hF : CoverPreserving J K F) : CoverPreserving J K G where
  cover_preserve {U S} hS := by
    apply K.superset_covering _ (K.pullback_stable (e.inv.app U) (hF.cover_preserve hS))
    rintro W a ⟨V, g, b, hg, hb⟩
    refine ⟨V, g, b ≫ e.hom.app V, hg, ?_⟩
    rw [Category.assoc, ← e.hom.naturality, ← Category.assoc, ← hb, Category.assoc]
    simp

private instance : (smallBaseChange i).IsContinuous (topology (domainGenerators X)) (topology (targetGenerators i)) := by
  have : RepresentablyFlat (smallBaseChange i) := flat_of_preservesFiniteLimits _
  apply Functor.isContinuous_iff_coverPreserving.mpr
  constructor
  intro V S hS
  rw [← (incl (targetGenerators i)).functorPushforward_mem_iff (topology (targetGenerators i)) Z.smallEtaleTopology,
    ← Sieve.functorPushforward_comp]
  have H : CoverPreserving (topology (domainGenerators X)) Z.smallEtaleTopology (incl (domainGenerators X) ⋙ baseChange i) := by
    constructor
    intro W R hR
    rw [Sieve.functorPushforward_comp]
    exact (PhilipponEtaleBaseChangeComparison.coverPreserving i).cover_preserve
      (((incl (domainGenerators X)).functorPushforward_mem_iff (topology (domainGenerators X)) X.smallEtaleTopology).mpr hR)
  exact (coverPreserving_of_iso (changeInclIso i).symm H).cover_preserve hS

private def smallPushforward : abelianSheaves (targetGenerators i) ⥤ abelianSheaves (domainGenerators X) :=
  (smallBaseChange i).sheafPushforwardContinuous _ _ _

private def changeSheavesIso :
    PhilipponEtaleClosedPushforward.pushforward i ⋙ restrictSheaves (domainGenerators X) ≅
      restrictSheaves (targetGenerators i) ⋙ smallPushforward i := by
  letI := Functor.isContinuous_comp (smallBaseChange i) (incl (targetGenerators i))
    (topology (domainGenerators X)) (topology (targetGenerators i)) Z.smallEtaleTopology
  exact Functor.sheafPushforwardContinuousComp' (changeInclIso i).symm _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

private instance smallKan (P : (ModelSite (domainGenerators X))ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallBaseChange i).op.HasLeftKanExtension P := by
  have (U : (ModelSite (targetGenerators i))ᵒᵖ) :
      HasColimitsOfShape (CostructuredArrow (smallBaseChange i).op U) AddCommGrpCat.{u} :=
    inferInstance
  infer_instance

private abbrev smallLan : ((ModelSite (domainGenerators X))ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
    ((ModelSite (targetGenerators i))ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (smallBaseChange i).op.lan

private def smallPullback : abelianSheaves (domainGenerators X) ⥤ abelianSheaves (targetGenerators i) := by
  let F : abelianSheaves (domainGenerators X) ⥤ ((ModelSite (domainGenerators X))ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    sheafToPresheaf (topology (domainGenerators X)) AddCommGrpCat.{u}
  let G : ((ModelSite (targetGenerators i))ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ abelianSheaves (targetGenerators i) :=
    presheafToSheaf (topology (targetGenerators i)) AddCommGrpCat.{u}
  exact F ⋙ smallLan i ⋙ G

private def smallAdjunction : smallPullback i ⊣ smallPushforward i :=
  (((smallBaseChange i).op.lanAdjunction AddCommGrpCat.{u}).comp
    (sheafificationAdjunction (topology (targetGenerators i)) AddCommGrpCat.{u})).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (topology (domainGenerators X)) AddCommGrpCat.{u}) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

private instance : PreservesFiniteLimits (smallPullback i) := by
  have : RepresentablyFlat (smallBaseChange i) := flat_of_preservesFiniteLimits _
  have : ReflectsLimits (forget AddCommGrpCat.{u}) := reflectsLimits_of_reflectsIsomorphisms
  have : PreservesFiniteLimits (smallLan i) :=
    lan_preservesFiniteLimits_of_flat (C := ModelSite (domainGenerators X)) (D := ModelSite (targetGenerators i)) _ (smallBaseChange i)
  have : PreservesFiniteLimits (smallLan i ⋙ presheafToSheaf (topology (targetGenerators i)) AddCommGrpCat.{u}) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

def pullbackSheaves : bigSheaves X ⥤ bigSheaves Z :=
  (restrictSheaves (domainGenerators X) ⋙ smallPullback i) ⋙ (restrictSheaves (targetGenerators i)).asEquivalence.inverse

private instance : PreservesFiniteLimits (pullbackSheaves i) := by
  have : PreservesFiniteLimits (restrictSheaves (domainGenerators X) ⋙ smallPullback i) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

private def pushforwardIso :
    restrictSheaves (targetGenerators i) ⋙ smallPushforward i ⋙ (restrictSheaves (domainGenerators X)).asEquivalence.inverse ≅
      PhilipponEtaleClosedPushforward.pushforward i :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (changeSheavesIso i).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictSheaves (domainGenerators X)).asEquivalence.unitIso.symm ≪≫
    Functor.rightUnitor _

def pullbackAdjunction :
    pullbackSheaves i ⊣ PhilipponEtaleClosedPushforward.pushforward i :=
  Adjunction.ofNatIsoRight
    (((restrictSheaves (domainGenerators X)).asEquivalence.toAdjunction.comp (smallAdjunction i)).comp
      (restrictSheaves (targetGenerators i)).asEquivalence.symm.toAdjunction)
    (pushforwardIso i)

/-- Direct image by a scheme morphism carries injective étale abelian
sheaves to injective étale abelian sheaves. -/
instance : (PhilipponEtaleClosedPushforward.pushforward i).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (pullbackAdjunction i)

end PhilipponEtaleSmallSite

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex


namespace PhilipponDerivedAdjunction

universe u v u' v' w w'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D]

private def homotopyAdjunction {L : D ⥤ C} {R : C ⥤ D} [L.Additive] [R.Additive]
    (adj : L ⊣ R) (c : ComplexShape ℕ) :
    L.mapHomotopyCategory c ⊣ R.mapHomotopyCategory c where
  unit := {
    app := (NatTrans.mapHomotopyCategory adj.unit c).app
    naturality := by
      rintro ⟨K⟩ ⟨M⟩ ⟨g : K ⟶ M⟩
      simp only [HomotopyCategory.quot_mk_eq_quotient_map, NatTrans.mapHomotopyCategory_app,
        Functor.id_map, Functor.comp_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
      congr 1
      ext n
      exact adj.unit.naturality (g.f n) }
  counit := {
    app := (NatTrans.mapHomotopyCategory adj.counit c).app
    naturality := by
      rintro ⟨K⟩ ⟨M⟩ ⟨g : K ⟶ M⟩
      simp only [HomotopyCategory.quot_mk_eq_quotient_map, NatTrans.mapHomotopyCategory_app,
        Functor.id_map, Functor.comp_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
      congr 1
      ext n
      exact adj.counit.naturality (g.f n) }
  left_triangle_components := by
    rintro ⟨K⟩
    simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp]
    congr 1
    ext n
    exact adj.left_triangle_components (K.X n)
  right_triangle_components := by
    rintro ⟨K⟩
    simp only [NatTrans.mapHomotopyCategory_app, Functor.mapHomotopyCategory_map,
      ← Functor.map_comp]
    congr 1
    ext n
    exact adj.right_triangle_components (K.X n)

private def homEquivOfIsos {E : Type*} [Category* E] [Preadditive E]
    {A B A' B' : E} (a : A ≅ A') (b : B ≅ B') : (A ⟶ B) ≃+ (A' ⟶ B') where
  toEquiv := Iso.homCongr a b
  map_add' := by simp [Iso.homCongr, Preadditive.add_comp, Preadditive.comp_add]

variable [HasInjectiveResolutions C]

/-- An injective-preserving left exact functor carries a resolution of an
acyclic object to an injective resolution of its image. -/
def mapInjectiveResolution (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R]
    [R.PreservesInjectiveObjects] {F : C} (I : InjectiveResolution F)
    (h : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj F)) :
    InjectiveResolution (R.obj F) where
  cocomplex := (R.mapHomologicalComplex _).obj I.cocomplex
  injective n := R.injective_obj_of_injective (I.injective n)
  ι := (singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).inv.app F ≫
    (R.mapHomologicalComplex _).map I.ι
  quasiIso := by
    constructor
    intro n
    cases n with
    | zero =>
      let K := (R.mapHomologicalComplex _).obj I.cocomplex
      let a : (CochainComplex.single₀ D).obj (R.obj F) ⟶ K :=
        (singleMapHomologicalComplex R (ComplexShape.up ℕ) 0).inv.app F ≫
          (R.mapHomologicalComplex _).map I.ι
      have eq : (singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (R.obj F)).inv ≫
          cyclesMap a 0 = I.toRightDerivedZero' R := by
        rw [← cancel_mono (K.iCycles 0), Category.assoc, cyclesMap_i,
          singleObjCyclesSelfIso_inv_iCycles_assoc, I.toRightDerivedZero'_comp_iCycles]
        simp only [a, comp_f, singleMapHomologicalComplex_inv_app_self,
          Functor.mapHomologicalComplex_map_f, Iso.inv_hom_id_assoc, Category.assoc,
          ← R.map_comp]
        congr 1
        have : (singleObjXSelf (ComplexShape.up ℕ) 0 F).inv = 𝟙 F := rfl
        rw [this, Category.id_comp]
      have : IsIso (cyclesMap a 0) := by
        rw [← isIso_comp_left_iff (singleObjCyclesSelfIso (ComplexShape.up ℕ) 0 (R.obj F)).inv,
          eq]
        infer_instance
      change QuasiIsoAt a 0
      rw [quasiIsoAt_iff_isIso_homologyMap]
      rw [← isIso_comp_left_iff (((CochainComplex.single₀ D).obj (R.obj F)).homologyπ 0),
        homologyπ_naturality]
      infer_instance
    | succ n =>
      apply (quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)).2
      exact (exactAt_iff_isZero_homology _ _).mpr (IsZero.of_iso (h n) (I.isoRightDerivedObj R _).symm)

private abbrev natEmbedding := ComplexShape.embeddingUpNat

private instance (E : Type*) [Category* E] [Abelian E] :
    (natEmbedding.extendHomotopyFunctor E).Additive where
  map_add {K M} f g := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
    let Q := HomotopyCategory.quotient E (ComplexShape.up ℕ)
    obtain ⟨(f : K ⟶ M), rfl⟩ := Q.map_surjective f
    obtain ⟨(g : K ⟶ M), rfl⟩ := Q.map_surjective g
    rw [← Q.map_add]
    change (natEmbedding.extendFunctor E ⋙ HomotopyCategory.quotient E _).map (f + g) = _
    rw [Functor.map_add]
    rfl

private def mapHomEquiv {E E' : Type*} [Category* E] [Category* E']
    [Preadditive E] [Preadditive E'] (G : E ⥤ E') [G.Additive] {A B : E}
    (h : Function.Bijective (G.map : (A ⟶ B) → _)) :
    (A ⟶ B) ≃+ (G.obj A ⟶ G.obj B) :=
  AddEquiv.ofBijective G.mapAddHom h

set_option maxHeartbeats 750000 in
private def extViaResolution {E : Type*} [Category* E] [Abelian E] [HasExt.{w} E]
    {F : E} (I : InjectiveResolution F) (P : E) (q : ℕ) :
    Ext P F q ≃+ ((HomotopyCategory.quotient E _).obj ((single E (ComplexShape.up ℕ) q).obj P) ⟶
      (HomotopyCategory.quotient E _).obj I.cocomplex) := by
  letI := HasDerivedCategory.standard E
  let Q := HomotopyCategory.quotient E (ComplexShape.up ℤ)
  let J := I.cocomplex.extend natEmbedding
  let K := (CochainComplex.singleFunctor E 0).obj P
  let a := (extendSingleIso natEmbedding F 0 0 rfl).inv ≫ extendMap I.ι natEmbedding
  have : QuasiIso a := by
    have : QuasiIso (extendMap I.ι natEmbedding) := (quasiIso_extendMap_iff _ _).mpr inferInstance
    dsimp only [a]
    infer_instance
  have : IsIso (DerivedCategory.Q.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso E a).mpr inferInstance
  let shiftH := shiftFunctor (HomotopyCategory E (ComplexShape.up ℤ)) (q : ℤ)
  let shiftD := shiftFunctor (DerivedCategory E) (q : ℤ)
  let eP := (DerivedCategory.singleFunctorIsoCompQ E 0).app P ≪≫
    (DerivedCategory.quotientCompQhIso E).symm.app K
  let eF := (DerivedCategory.singleFunctorIsoCompQ E 0).app F ≪≫
    asIso (DerivedCategory.Q.map a) ≪≫ (DerivedCategory.quotientCompQhIso E).symm.app J
  let eShift := (DerivedCategory.Qh.commShiftIso (q : ℤ)).app (Q.obj J)
  let eQ := (Q.commShiftIso (q : ℤ)).app J
  let eq := (HomotopyCategory.singleFunctors E).shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)
  let eSingle := Q.mapIso (extendSingleIso natEmbedding P q (q : ℤ) rfl)
  let eSource := shiftH.mapIso eSingle ≪≫ eq.app P
  let e₁ : Ext P F q ≃+ _ := Ext.homAddEquiv.trans
    (homEquivOfIsos eP (shiftD.mapIso eF ≪≫ eShift.symm ≪≫ DerivedCategory.Qh.mapIso eQ.symm))
  have : CochainComplex.IsKInjective (J⟦(q : ℤ)⟧) :=
    (CochainComplex.isKInjective_shift_iff J _).mpr inferInstance
  let e₂ := mapHomEquiv DerivedCategory.Qh
    (A := Q.obj K) (B := Q.obj (J⟦(q : ℤ)⟧)) (CochainComplex.IsKInjective.Qh_map_bijective _ _)
  let e₃ := homEquivOfIsos (Iso.refl (Q.obj K)) eQ
  let extend := natEmbedding.extendHomotopyFunctor E
  let e₄ := mapHomEquiv extend
    (A := (HomotopyCategory.quotient E _).obj ((single E (ComplexShape.up ℕ) q).obj P))
    (B := (HomotopyCategory.quotient E _).obj I.cocomplex)
    ⟨extend.map_injective, extend.map_surjective⟩
  let e₅ := mapHomEquiv shiftH
    (A := Q.obj (((single E (ComplexShape.up ℕ) q).obj P).extend natEmbedding))
    (B := Q.obj J) ⟨shiftH.map_injective, shiftH.map_surjective⟩
  exact e₁.trans (e₂.symm.trans (e₃.trans
    ((homEquivOfIsos eSource.symm (Iso.refl _)).trans (e₅.symm.trans e₄.symm))))

/-- The Ext adjunction at an acyclic value of an injective-preserving right adjoint. -/
def extEquivOfAcyclic [HasExt.{w} C] [HasExt.{w'} D]
    {L : D ⥤ C} {R : C ⥤ D} [L.Additive] [R.Additive] [PreservesFiniteLimits R]
    [R.PreservesInjectiveObjects] (adj : L ⊣ R) {F : C}
    (h : ∀ q : ℕ, IsZero ((R.rightDerived (q + 1)).obj F)) (P : D) (q : ℕ) :
    Ext P (R.obj F) q ≃+ Ext (L.obj P) F q := by
  let I := injectiveResolution F
  let J := mapInjectiveResolution R I h
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℕ)
  let s := (singleMapHomologicalComplex L (ComplexShape.up ℕ) q).app P
  exact (extViaResolution J P q).trans
    (((homotopyAdjunction adj _).homAddEquiv _ (Q.obj I.cocomplex)).symm.trans
      ((homEquivOfIsos (Q.mapIso s) (Iso.refl _)).trans (extViaResolution I (L.obj P) q).symm))

end PhilipponDerivedAdjunction

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtaleAcyclicCohomology

universe u

private abbrev AbelianSheaves (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{u}) :
    HasExt.{u} (AbelianSheaves X) := inferInstance

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def isTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

private def terminalComparison {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (baseChange f).obj (terminal X) ≅ terminal Y := by
  have : PreservesFiniteLimits (baseChange f) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))
  exact (IsTerminal.isTerminalObj (baseChange f) _ (isTerminal X)).uniqueUpToIso (isTerminal Y)

private abbrev globalSections (X : Scheme.{u}) :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (terminal X))

private def globalSectionsIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    pushforward f ⋙ globalSections X ≅ globalSections Y :=
  NatIso.ofComponents (fun F => F.obj.mapIso (terminalComparison f).symm.op) (fun g =>
    (g.hom.naturality (terminalComparison f).inv.op).symm)

/-- Pullback on small étale sheaves preserves the constant sheaf functor. -/
def pullbackConstantIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙ pullbackSheaves f ≅
      constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  let adj := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} (isTerminal X)).comp
    (pullbackAdjunction f)
  (Adjunction.ofNatIsoRight adj (globalSectionsIso f)).leftAdjointUniq
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} (isTerminal Y))

/-- A sheaf with zero higher direct images has the same cohomology as its
direct image on the target. -/
def cohomologyEquiv {X Y : Scheme.{u}} (f : Y ⟶ X) (F : AbelianSheaves Y)
    (h : ∀ q : ℕ, IsZero (((pushforward f).rightDerived (q + 1)).obj F)) (n : ℕ) :
    ((pushforward f).obj F).H n ≃+ F.H n := by
  let adj := pullbackAdjunction f
  have : (pullbackSheaves f).Additive := adj.left_adjoint_additive
  let P := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))
  let e := (pullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))
  let eExt := ((extFunctor n).mapIso e.symm.op).app F
  exact (PhilipponDerivedAdjunction.extEquivOfAcyclic adj h P n).trans
    eExt.addCommGroupIsoToAddEquiv

end PhilipponEtaleAcyclicCohomology

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (h : ∀ q : ℕ, IsZero (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived (q + 1)).obj F)) (n : ℕ) :
    Nonempty (((PhilipponEtaleClosedPushforward.pushforward f).obj F).H n ≃+ F.H n) := by
  exact ⟨PhilipponEtaleAcyclicCohomology.cohomologyEquiv f F h n⟩


end
