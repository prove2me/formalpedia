-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_geometric_stalk_equiv_fiber_cohomology_zero_of_proper_excision
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-20T22:04:08.93412+00:00
-- url     : https://prove2.me/submissions/1bbabcca-85e5-40b8-b706-fefd4b38a9d7

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas

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

open AlgebraicGeometry CategoryTheory Opposite
namespace PhilipponEtaleAcyclicCohomology
universe u
abbrev globalSections (X : Scheme.{u}) :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (Scheme.Etale.mk (𝟙 X)))
end PhilipponEtaleAcyclicCohomology

end

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

open Set Topology

namespace PhilipponClosedCoverContinuousMaps

variable {X Y Z A : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace A]

private theorem continuousOn_range {p : Y → X} (hp : IsEmbedding p)
    {h : X → A} (f : C(Y, A)) (hres : ∀ y, h (p y) = f y) :
    ContinuousOn h (range p) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (range p).domRestrict h = f ∘ hp.toHomeomorph.symm := by
    funext x
    obtain ⟨y, rfl⟩ := hp.toHomeomorph.surjective x
    simpa only [Set.domRestrict_apply, Function.comp_apply, Homeomorph.symm_apply_apply,
      IsEmbedding.toHomeomorph_apply_coe] using hres y
  rw [he]
  exact f.continuous.comp hp.toHomeomorph.symm.continuous

/-- Compatible continuous maps on two closed subspaces glue on their union. -/
theorem exists_glue {p : Y → X} {q : Z → X}
    (hp : IsClosedEmbedding p) (hq : IsClosedEmbedding q)
    (hcover : range p ∪ range q = univ) (f : C(Y, A)) (g : C(Z, A))
    (hagree : ∀ y z, p y = q z → f y = g z) :
    ∃ h : C(X, A), (∀ y, h (p y) = f y) ∧ ∀ z, h (q z) = g z := by
  classical
  have hr (x : X) (hx : x ∉ range p) : x ∈ range q := by
    have : x ∈ range p ∪ range q := hcover.symm ▸ mem_univ x
    exact this.resolve_left hx
  let h (x : X) := if hx : x ∈ range p then f hx.choose else g (hr x hx).choose
  have hleft (y : Y) : h (p y) = f y := by
    have hy : p y ∈ range p := mem_range_self y
    simp only [h, dif_pos hy, hp.injective hy.choose_spec]
  have hright (z : Z) : h (q z) = g z := by
    by_cases hz : q z ∈ range p
    · simp only [h, dif_pos hz]
      exact hagree _ z hz.choose_spec
    · simp only [h, dif_neg hz, hq.injective (hr (q z) hz).choose_spec]
  have hc := (continuousOn_range hp.isEmbedding f hleft).union_of_isClosed
    (continuousOn_range hq.isEmbedding g hright) hp.isClosed_range hq.isClosed_range
  rw [hcover, continuousOn_univ] at hc
  exact ⟨⟨h, hc⟩, hleft, hright⟩

/-- Descent of a continuous function along a closed map that has singleton
fibres off a closed set, when the function vanishes over that set. -/
theorem existsUnique_descend_zero [Zero A] {p : Y → X} (hp : Continuous p)
    (hclosed : IsClosedMap p) {S : Set X} (hS : IsClosed S)
    (hcover : range p ∪ S = univ)
    (hinj : ∀ {y z : Y}, p y = p z → p y ∉ S → y = z)
    (a : C(Y, A)) (ha : ∀ y, p y ∈ S → a y = 0) :
    ∃! b : C(X, A), (∀ x ∈ S, b x = 0) ∧ ∀ y, b (p y) = a y := by
  let r : C(Y, range p) := ⟨rangeFactorization p, continuous_rangeFactorization_iff.mpr hp⟩
  have hr : IsClosedMap r := by
    intro T hT
    have h : r '' T = Subtype.val ⁻¹' (p '' T) := by
      ext x
      exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, congrArg Subtype.val h⟩,
        fun ⟨y, hy, h⟩ => ⟨y, hy, Subtype.ext h⟩⟩
    rw [h]
    exact (hclosed T hT).preimage continuous_subtype_val
  let hq := hr.isQuotientMap r.continuous rangeFactorization_surjective
  have hfactor : Function.FactorsThrough a r := by
    intro y z he
    have he' : p y = p z := congrArg Subtype.val he
    by_cases h : p y ∈ S
    · rw [ha y h, ha z (he' ▸ h)]
    · rw [hinj he' h]
  let c := hq.lift a hfactor
  have hc (y : Y) : c (r y) = a y := DFunLike.congr_fun (hq.lift_comp a hfactor) y
  have hagree (y : range p) (z : S) (h : y.val = z.val) : c y = (0 : A) := by
    obtain ⟨t, ht⟩ := hq.surjective y
    rw [← ht, hc]
    apply ha
    change (r t).val ∈ S
    rw [ht, h]
    exact z.property
  obtain ⟨b, hb, hb₀⟩ := exists_glue hclosed.isClosed_range.isClosedEmbedding_subtypeVal
    hS.isClosedEmbedding_subtypeVal (by rwa [Subtype.range_coe, Subtype.range_coe])
    c (ContinuousMap.const S 0) hagree
  refine ⟨b, ⟨fun x hx => hb₀ ⟨x, hx⟩, fun y => (hb (r y)).trans (hc y)⟩, ?_⟩
  intro b' hb'
  ext x
  have hx : x ∈ range p ∪ S := hcover.symm ▸ mem_univ x
  rcases hx with ⟨y, rfl⟩ | hx
  · exact (hb'.2 y).trans ((hb (r y)).trans (hc y)).symm
  · exact (hb'.1 x hx).trans (hb₀ ⟨x, hx⟩).symm

/-- Near any point of the ambient space, a continuous map from a closed
subspace to a discrete set takes a single value on the part of the subspace
in that neighborhood. -/
theorem exists_open_constant [DiscreteTopology A] [Nonempty A] {p : Y → X}
    (hp : IsClosedEmbedding p) (f : C(Y, A)) (x : X) :
    ∃ (U : Set X) (_ : IsOpen U) (_ : x ∈ U) (a : A), ∀ y, p y ∈ U → f y = a := by
  classical
  by_cases hx : x ∈ range p
  · obtain ⟨y, rfl⟩ := hx
    let B := (f ⁻¹' ({f y} : Set A))ᶜ
    have hB : IsClosed B := ((isOpen_discrete _).preimage f.continuous).isClosed_compl
    refine ⟨(p '' B)ᶜ, (hp.isClosedMap _ hB).isOpen_compl, ?_, f y, ?_⟩
    · rintro ⟨z, hz, he⟩
      have := hp.injective he
      subst z
      exact hz rfl
    · intro z hz
      by_contra hne
      exact hz ⟨z, hne, rfl⟩
  · exact ⟨(range p)ᶜ, hp.isClosed_range.isOpen_compl, hx, Classical.arbitrary A,
      fun y hy => (hy (mem_range_self y)).elim⟩

end PhilipponClosedCoverContinuousMaps

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponEtaleProperRelativeMaps

universe u v

/-- Being an isomorphism on an open subset survives arbitrary base change. -/
theorem isIso_restrict_baseChange {X Y V : Scheme.{u}} (f : Y ⟶ X) (v : V ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] : IsIso (pullback.fst v f ∣_ (v ⁻¹ᵁ U)) := by
  have h₁ := (isPullback_morphismRestrict (pullback.fst v f) (v ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback v f).flip
  have h₂ := (IsPullback.of_hasPullback (v ∣_ U) (f ∣_ U)).flip.paste_horiz
    (isPullback_morphismRestrict f U).flip
  rw [morphismRestrict_ι] at h₂
  let e := h₁.isoIsPullback _ _ h₂
  have he : e.hom ≫ pullback.fst (v ∣_ U) (f ∣_ U) = pullback.fst v f ∣_ (v ⁻¹ᵁ U) :=
    h₁.isoIsPullback_hom_snd _ _ h₂
  rw [← he]
  infer_instance

/-- A base change with image in an open subset where the map is an
isomorphism is an isomorphism over the entire new base. -/
theorem isIso_baseChange_of_range_subset {X Y V : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] (v : V ⟶ X) (hv : Set.range v ⊆ (U : Set X)) :
    IsIso (pullback.fst v f) := by
  have hU : v ⁻¹ᵁ U = ⊤ := top_le_iff.mp (fun x _ => hv (Set.mem_range_self x))
  have h := isIso_restrict_baseChange f v U
  rw [hU] at h
  have hc : IsIso ((pullback.fst v f ∣_ ⊤) ≫ (⊤ : V.Opens).ι) := by
    rw [← Scheme.topIso_hom]
    infer_instance
  rw [morphismRestrict_ι, Scheme.Hom.preimage_top, ← Scheme.topIso_hom] at hc
  exact (isIso_comp_left_iff _ _).mp hc

/-- A geometric fiber outside the center of an excision square is the
geometric point itself. -/
theorem isIso_geometricFiber_of_mem {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s default ∈ U) : IsIso (pullback.fst s f) := by
  apply isIso_baseChange_of_range_subset f U s
  rintro _ ⟨x, rfl⟩
  rwa [Subsingleton.elim x default]

/-- The image of a base change over the center is contained in the
exceptional closed subset. -/
theorem range_snd_subset_exceptional {X Y Z V : Scheme.{u}} (f : Y ⟶ X) (i : Z ⟶ X)
    (v : V ⟶ X) (h : Set.range v ⊆ Set.range i) :
    Set.range (pullback.snd v f) ⊆ Set.range (pullback.fst f i) := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Pullback.range_fst]
  change f (pullback.snd v f y) ∈ Set.range i
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  exact h (Set.mem_range_self _)

/-- A function on the modification that vanishes on the exceptional
inverse image descends uniquely to a function vanishing on the center. -/
theorem existsUnique_descend_zero {X Y Z : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (f ∣_ U)]
    (hU : Set.range i = (U : Set X)ᶜ)
    {A : Type v} [TopologicalSpace A] [Zero A] (a : C(Y, A))
    (ha : ∀ t : ↥(pullback f i), a (pullback.fst f i t) = 0) :
    ∃! b : C(X, A), (∀ x ∈ Set.range i, b x = 0) ∧ ∀ y, b (f y) = a y := by
  have point (y : (f ⁻¹ᵁ U).toScheme) : ((f ∣_ U) y).val = f y.val :=
    congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ X => k y) (morphismRestrict_ι f U)
  have hcover : Set.range f ∪ Set.range i = Set.univ := by
    rw [hU]
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨y, hy⟩ := (f ∣_ U).surjective ⟨x, hx⟩
      exact Or.inl ⟨y.val, (point y).symm.trans (congrArg Subtype.val hy)⟩
    · exact Or.inr hx
  have hinj {y z : Y} (h : f y = f z) (hy : f y ∉ Set.range i) : y = z := by
    rw [hU] at hy
    have hy' : f y ∈ (U : Set X) := by simpa only [Set.mem_compl_iff, not_not] using hy
    have hz' : f z ∈ (U : Set X) := h ▸ hy'
    let y' : (f ⁻¹ᵁ U).toScheme := ⟨y, hy'⟩
    let z' : (f ⁻¹ᵁ U).toScheme := ⟨z, hz'⟩
    have hs : (f ∣_ U) y' = (f ∣_ U) z' := Subtype.ext ((point y').trans (h.trans (point z').symm))
    exact congrArg (fun t : (f ⁻¹ᵁ U).toScheme => t.val) ((f ∣_ U).homeomorph.injective hs)
  refine PhilipponClosedCoverContinuousMaps.existsUnique_descend_zero
    f.continuous f.isClosedMap i.isClosedEmbedding.isClosed_range hcover hinj a ?_
  rintro y ⟨z, hz⟩
  obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback f i) y z hz.symm
  rw [← ht]
  exact ha t

section Additive

variable {X Y Z : Scheme.{u}} (A : Type v) [AddCommGroup A] [TopologicalSpace A]
  [DiscreteTopology A]

/-- The subgroup of continuous coefficient functions that vanish along a
given scheme morphism. -/
def vanishingFunctions (i : Z ⟶ X) : AddSubgroup C(X, A) where
  carrier := {a | ∀ z : Z, a (i z) = 0}
  zero_mem' := fun _ => rfl
  add_mem' ha hb z := by
    change _ + _ = (0 : A)
    rw [ha z, hb z, add_zero]
  neg_mem' ha z := by
    change -_ = (0 : A)
    rw [ha z, neg_zero]

private def pullbackFunctions (f : Y ⟶ X) (i : Z ⟶ X) :
    vanishingFunctions A i →+ vanishingFunctions A (pullback.fst f i) where
  toFun a := ⟨a.val.comp ⟨f, f.continuous⟩, by
    intro t
    change a.val (f (pullback.fst f i t)) = 0
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact a.property (pullback.snd f i t)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Degree-zero relative coefficient functions are unchanged by pullback
along a proper modification over the complement. -/
noncomputable def functionsEquiv (f : Y ⟶ X) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (f ∣_ U)]
    (hU : Set.range i = (U : Set X)ᶜ) :
    vanishingFunctions A i ≃+ vanishingFunctions A (pullback.fst f i) := by
  apply AddEquiv.ofBijective (pullbackFunctions A f i)
  apply (Function.bijective_iff_existsUnique _).mpr
  intro a
  obtain ⟨b, hb, hu⟩ := existsUnique_descend_zero f i U hU a.val a.property
  refine ⟨⟨b, fun z => hb.1 (i z) (Set.mem_range_self z)⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply ContinuousMap.ext
    intro y
    exact hb.2 y
  · intro c hc
    apply Subtype.ext
    refine hu c.val ⟨?_, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact c.property z
    · intro y
      exact congrArg (fun k : vanishingFunctions A (pullback.fst f i) => k.val y) hc

/-- The descent equivalence holds after any base change of a proper
excision square. -/
noncomputable def functionsEquiv_baseChange {V : Scheme.{u}} (v : V ⟶ X) (f : Y ⟶ X) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (f ∣_ U)]
    (hU : Set.range i = (U : Set X)ᶜ) :
    vanishingFunctions A (pullback.fst v i) ≃+
      vanishingFunctions A (pullback.fst (pullback.fst v f) (pullback.fst v i)) := by
  have : IsIso (pullback.fst v f ∣_ (v ⁻¹ᵁ U)) := isIso_restrict_baseChange f v U
  refine functionsEquiv A (pullback.fst v f) (pullback.fst v i) (v ⁻¹ᵁ U) ?_
  rw [Scheme.Pullback.range_fst, hU, Set.preimage_compl]
  rfl

end Additive

end PhilipponEtaleProperRelativeMaps

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleClosedCover (restriction)
namespace PhilipponEtaleRelativeCohomology
universe u
variable {X Z : Scheme.{u}} (i : Z ⟶ X)
variable (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
/-- Sections of the relative sheaf are exactly the kernel of the
restriction map on the chosen étale object. -/
def relativeSections (W : X.Etaleᵒᵖ) :
    (relativeSheaf i A).obj.obj W ≃+
      (((sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj W).map
        (restriction A i)).hom.ker := by
  let F := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj W
  have : F.Additive := ⟨by intros; rfl⟩
  let G := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙ (evaluation _ _).obj W
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso (Iso.refl _ : G ≅ F)
  exact ((PreservesKernel.iso F (restriction A i)) ≪≫
    AddCommGrpCat.kernelIsoKer (F.map (restriction A i))).addCommGroupIsoToAddEquiv

end PhilipponEtaleRelativeCohomology

end

section

set_option autoImplicit false
set_option maxHeartbeats 550000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleProperRelativeMaps (vanishingFunctions functionsEquiv_baseChange)
open PhilipponEtaleRelativeCohomology (relativeSheaf relativeSections relativeConstant)


namespace PhilipponEtaleRelativeDirectImage

universe u

private def subgroupEquiv {B : Type u} [AddCommGroup B] {P Q : AddSubgroup B} (h : P = Q) : P ≃+ Q := by
  subst Q
  exact AddEquiv.refl P

@[simp] private theorem subgroupEquiv_val {B : Type u} [AddCommGroup B] {P Q : AddSubgroup B}
    (h : P = Q) (b : P) : (subgroupEquiv h b).val = b.val := by
  subst Q
  rfl

variable {X Y Z : Scheme.{u}} (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private theorem vanishingFunctions_eq_of_range {B C D : Scheme.{u}}
    (a : C ⟶ B) (b : D ⟶ B) (h : Set.range a = Set.range b) :
    vanishingFunctions A a = vanishingFunctions A b := by
  ext w
  change (∀ x : C, w (a x) = 0) ↔ (∀ x : D, w (b x) = 0)
  constructor
  · intro hw x
    obtain ⟨y, hy⟩ := h.symm ▸ Set.mem_range_self (f := b) x
    exact hy ▸ hw y
  · intro hw x
    obtain ⟨y, hy⟩ := h ▸ Set.mem_range_self (f := a) x
    exact hy ▸ hw y

private abbrev sectionsAt (W : X.Etale) := (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op W)

private theorem sectionKernel (i : Z ⟶ X) (W : X.Etale) :
    (((sectionsAt W).map (restriction A i)).hom.ker : AddSubgroup C(W.left, A)) =
      vanishingFunctions A (pullback.fst W.hom i) := by
  ext a
  change C(W.left, A) at a
  change ((sectionsAt W).map (restriction A i)).hom a = 0 ↔
    ∀ z : ↥(pullback W.hom i), a (pullback.fst W.hom i z) = 0
  constructor
  · intro h z
    exact congrArg (fun s : C(↥(pullback W.hom i), A) => s z) h
  · intro h
    exact ContinuousMap.ext h

/-- Evaluate the relative sheaf as functions vanishing along the closed
inverse image in an étale object. -/
def sectionFunctions (i : Z ⟶ X) (W : X.Etale) :
    (relativeSheaf i A).obj.obj (op W) ≃+ vanishingFunctions A (pullback.fst W.hom i) :=
  (relativeSections i A (op W)).trans (subgroupEquiv (sectionKernel A i W))

private theorem sectionFunctions_val (i : Z ⟶ X) (W : X.Etale) (s : (relativeSheaf i A).obj.obj (op W)) :
    (sectionFunctions A i W s).val = ((kernel.ι (restriction A i)).hom.app (op W)) s := by
  calc
    _ = (relativeSections i A (op W) s).val := subgroupEquiv_val _ _
    _ = _ := by
      let F := sectionsAt W
      let G := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙ (evaluation _ _).obj (op W)
      have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
      have : PreservesFiniteLimits F := preservesFiniteLimits_of_natIso (Iso.refl _ : G ≅ F)
      have eq : ((PreservesKernel.iso F (restriction A i)).hom ≫
          (AddCommGrpCat.kernelIsoKer (F.map (restriction A i))).hom) ≫
          AddCommGrpCat.ofHom (AddSubgroup.subtype (F.map (restriction A i)).hom.ker) =
          F.map (kernel.ι (restriction A i)) := by
        simp only [Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
          PreservesKernel.iso_hom, kernelComparison_comp_ι]
      exact ConcreteCategory.congr_hom eq s

/-- Restriction of a relative section corresponds to precomposition with the
morphism of étale objects. -/
theorem sectionFunctions_map (i : Z ⟶ X) {V W : X.Etale} (g : V ⟶ W)
    (s : (relativeSheaf i A).obj.obj (op W)) (x : V.left) :
    (sectionFunctions A i V ((relativeSheaf i A).obj.map g.op s)).val x =
      (sectionFunctions A i W s).val (g.left x) := by
  rw [sectionFunctions_val, sectionFunctions_val]
  have h := congrArg (fun t : C(V.left, A) => t x)
    (NatTrans.naturality_apply (kernel.ι (restriction A i)).hom g.op s)
  exact h

private theorem range_pullback_centers (v : X.Etale) (f : Y ⟶ X) (i : Z ⟶ X) :
    Set.range (pullback.fst (pullback.fst v.hom f) (pullback.fst v.hom i)) =
      Set.range (pullback.fst (pullback.snd v.hom f) (pullback.fst f i)) := by
  ext x
  simp only [Scheme.Pullback.range_fst, Set.mem_preimage]
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  rfl

variable (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
  (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)

private def sectionComparison (W : X.Etale) :
    (relativeSheaf i A).obj.obj (op W) ≃+
      (relativeSheaf (pullback.fst f i) A).obj.obj (op ((baseChange f).obj W)) :=
  (sectionFunctions A i W).trans ((functionsEquiv_baseChange A W.hom f i U hU).trans
    ((subgroupEquiv (vanishingFunctions_eq_of_range A _ _ (range_pullback_centers W f i))).trans
      (sectionFunctions A (pullback.fst f i) ((baseChange f).obj W)).symm))

private theorem sectionComparison_apply (W : X.Etale) (s : (relativeSheaf i A).obj.obj (op W))
    (y : ((baseChange f).obj W).left) :
    (sectionFunctions A (pullback.fst f i) ((baseChange f).obj W)
      (sectionComparison A f i U hU W s)).val y =
      (sectionFunctions A i W s).val (pullback.fst W.hom f y) := by
  let b := functionsEquiv_baseChange A W.hom f i U hU (sectionFunctions A i W s)
  let e := sectionFunctions A (pullback.fst f i) ((baseChange f).obj W)
  let c := subgroupEquiv (vanishingFunctions_eq_of_range A _ _ (range_pullback_centers W f i)) b
  calc
    _ = c.val y := congrArg (fun z => z.val y) (e.apply_symm_apply c)
    _ = b.val y := congrArg (fun z : C((pullback W.hom f : Scheme.{u}), A) => z y)
      (subgroupEquiv_val _ b)
    _ = _ := rfl

/-- The relative sheaf on the target is the direct image of the relative
sheaf on the source of a proper excision square. -/
def relativeDirectImageIso :
    relativeSheaf i A ≅ (pushforward f).obj (relativeSheaf (pullback.fst f i) A) := by
  apply (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
  refine NatIso.ofComponents (fun W => (sectionComparison A f i U hU W.unop).toAddCommGrpIso) ?_
  intro W V g
  apply ConcreteCategory.hom_ext
  intro s
  apply (sectionFunctions A (pullback.fst f i) ((baseChange f).obj V.unop)).injective
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change (sectionFunctions A (pullback.fst f i) ((baseChange f).obj V.unop)
      (sectionComparison A f i U hU V.unop ((relativeSheaf i A).obj.map g s))).val y =
    (sectionFunctions A (pullback.fst f i) ((baseChange f).obj V.unop)
      ((relativeSheaf (pullback.fst f i) A).obj.map ((baseChange f).map g.unop).op
        (sectionComparison A f i U hU W.unop s))).val y
  rw [sectionComparison_apply, sectionFunctions_map, sectionComparison_apply]
  calc
    _ = (sectionFunctions A i W.unop s).val (g.unop.left (pullback.fst V.unop.hom f y)) :=
      sectionFunctions_map A i g.unop s (pullback.fst V.unop.hom f y)
    _ = _ := congrArg (sectionFunctions A i W.unop s).val
      (congrArg (fun k : ((baseChange f).obj V.unop).left ⟶ W.unop.left => k y)
        (map_isPullback f g.unop).w)

/-- The direct-image comparison with the canonical discrete topology. -/
def relativeConstantDirectImageIso :
    relativeConstant i A ≅ (pushforward f).obj (relativeConstant (pullback.fst f i) A) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact relativeDirectImageIso A f i U hU

end PhilipponEtaleRelativeDirectImage

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject


namespace PhilipponEtaleGeometricStalks

universe u

/-- A geometric point given by a separable closure of the residue field. -/
def geometricMap {X : Scheme.{u}} (x : X) :
    Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ X :=
  (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
    ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩

@[simp] theorem geometricMap_apply {X : Scheme.{u}} (x : X) : geometricMap x default = x := by
  simp [geometricMap, Scheme.SpecToEquivOfField]

/-- The point on the small étale site associated to `geometricMap`. -/
abbrev geometricPoint {X : Scheme.{u}} (x : X) : X.smallEtaleTopology.Point :=
  Scheme.pointSmallEtale (geometricMap x)

/-- An étale abelian sheaf vanishes if its geometric stalks vanish. -/
theorem isZero_of_stalks {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (h : ∀ x : X, IsZero ((geometricPoint x).sheafFiber.obj F)) : IsZero F := by
  let t : F ⟶ 0 := 0
  have ht : IsIso t := by
    let P := ObjectProperty.ofObj (fun x : X => geometricPoint x)
    have hP : P.IsConservativeFamilyOfPoints :=
      Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
    refine ((hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff t).mpr ?_
    intro Φ
    have hp := Φ.property
    change ObjectProperty.ofObj (fun x : X => geometricPoint x) Φ.obj at hp
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp hp
    rw [← hx]
    exact (h x).isIso ((geometricPoint x).sheafFiber.map_isZero (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso t)

end PhilipponEtaleGeometricStalks

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtaleStalkPullback

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ Y)

/-- The two projections of a pullback identify geometric lifts over the
source with geometric lifts over the target. -/
def pointFiberIso :
    baseChange f ⋙ (Scheme.pointSmallEtale s).fiber ≅ (Scheme.pointSmallEtale (s ≫ f)).fiber := by
  refine NatIso.ofComponents (fun W => Equiv.toIso ?_) ?_
  · let p := pullback.fst W.hom f
    let q := pullback.snd W.hom f
    change (Over.mk s ⟶ Over.mk q) ≃ (Over.mk (s ≫ f) ⟶ Over.mk W.hom)
    refine {
      toFun := fun t => Over.homMk (t.left ≫ p) (by
        change (t.left ≫ pullback.fst W.hom f) ≫ W.hom = s ≫ f
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ f) (Over.w t))
      invFun := fun t => Over.homMk (pullback.lift t.left s (Over.w t)) (pullback.lift_snd _ _ _)
      left_inv := ?_
      right_inv := ?_ }
    · intro t
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · exact pullback.lift_fst _ _ _
      · exact (pullback.lift_snd _ _ _).trans (Over.w t).symm
    · intro t
      apply Over.OverMorphism.ext
      exact pullback.lift_fst _ _ _
  · intro W V g
    apply ConcreteCategory.hom_ext
    intro t
    apply Over.OverMorphism.ext
    change (t.left ≫ ((baseChange f).map g).left) ≫ pullback.fst V.hom f =
      (t.left ≫ pullback.fst W.hom f) ≫ g.left
    simp only [Category.assoc]
    rw [(map_isPullback f g).w]

theorem pointFiberIso_inv_fst (W : X.Etale)
    (x : (Scheme.pointSmallEtale (s ≫ f)).fiber.obj W) :
    ((pointFiberIso f s).inv.app W x).left ≫ pullback.fst W.hom f = x.left :=
  pullback.lift_fst _ _ _

private def skyscraperIso :
    (Scheme.pointSmallEtale s).skyscraperSheafFunctor ⋙ pushforward f ≅
      (Scheme.pointSmallEtale (s ≫ f)).skyscraperSheafFunctor := by
  let e := (flipFunctor _ _ _).mapIso
    (Functor.isoWhiskerRight (NatIso.op (pointFiberIso f s).symm) (piFunctor.{u}.flip :
      (Type u)ᵒᵖ ⥤ AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}))
  let ff := fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}
  refine NatIso.ofComponents (fun M => ff.preimageIso (e.app M)) ?_
  intro M N a
  apply ff.map_injective
  exact e.hom.naturality a

/-- The geometric stalk of an inverse image is the stalk at the composite
geometric point. -/
def stalkPullbackIso :
    pullbackSheaves f ⋙ (Scheme.pointSmallEtale s).sheafFiber ≅
      (Scheme.pointSmallEtale (s ≫ f)).sheafFiber :=
  (Adjunction.ofNatIsoRight
    ((pullbackAdjunction f).comp (Scheme.pointSmallEtale s).skyscraperSheafAdjunction)
    (skyscraperIso f s)).leftAdjointUniq (Scheme.pointSmallEtale (s ≫ f)).skyscraperSheafAdjunction

end PhilipponEtaleStalkPullback

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleRelativeCohomology (relativeSheaf relativeConstant)
open PhilipponEtaleRelativeDirectImage (sectionFunctions sectionFunctions_map)


namespace PhilipponEtaleRelativeStalks

universe u

section Sections

variable {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Type u) [AddCommGroup A]
  [TopologicalSpace A] [DiscreteTopology A] {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X)

private abbrev Φ := Scheme.pointSmallEtale s
private abbrev P := (relativeSheaf i A).obj

private abbrev pointOfNeighborhood {W : X.Etale} (t : (Φ s).fiber.obj W) : W.left :=
  t.left (default : Spec (CommRingCat.of K))

private theorem exists_refinement_of_same_value {W : X.Etale} (t : (Φ s).fiber.obj W)
    (a b : ↥((P i A).obj (op W)))
    (h : (sectionFunctions A i W a).val (pointOfNeighborhood s t) =
      (sectionFunctions A i W b).val (pointOfNeighborhood s t)) :
    ∃ (V : X.Etale) (g : V ⟶ W) (t' : (Φ s).fiber.obj V),
      (Φ s).fiber.map g t' = t ∧ (P i A).map g.op a = (P i A).map g.op b := by
  let d := (sectionFunctions A i W a).val - (sectionFunctions A i W b).val
  let D : W.left.Opens := ⟨d ⁻¹' {0}, (isOpen_discrete _).preimage d.continuous⟩
  let V := Scheme.Etale.mk (D.ι ≫ W.hom)
  let g : V ⟶ W := MorphismProperty.Over.homMk D.ι rfl trivial
  let tLeft : Spec (CommRingCat.of K) ⟶ W.left := t.left
  have hD : Set.range tLeft ⊆ Set.range D.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w default, Scheme.Opens.range_ι]
    exact sub_eq_zero.mpr h
  let q := IsOpenImmersion.lift D.ι tLeft hD
  have hq : q ≫ D.ι = tLeft := IsOpenImmersion.lift_fac _ _ _
  let t' : (Φ s).fiber.obj V := Over.homMk q (by
    change q ≫ D.ι ≫ W.hom = s
    rw [← Category.assoc, hq]
    exact Over.w t)
  refine ⟨V, g, t', Over.OverMorphism.ext hq, ?_⟩
  apply (sectionFunctions A i V).injective
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  rw [sectionFunctions_map A i g, sectionFunctions_map A i g]
  exact sub_eq_zero.mp (show d (D.ι y) = 0 from y.property)

private def sectionEvaluation (W : X.Etale) (t : (Φ s).fiber.obj W) :
    (P i A).obj (op W) ⟶ AddCommGrpCat.of A :=
  AddCommGrpCat.ofHom {
    toFun := fun a => (sectionFunctions A i W a).val (pointOfNeighborhood s t)
    map_zero' := congrArg (fun a => a.val (pointOfNeighborhood s t)) (map_zero (sectionFunctions A i W))
    map_add' := fun a b => congrArg (fun a => a.val (pointOfNeighborhood s t))
      (map_add (sectionFunctions A i W) a b) }

private def stalkEvaluation : (Φ s).presheafFiber.obj (P i A) ⟶ AddCommGrpCat.of A :=
  (Φ s).presheafFiberDesc (sectionEvaluation i A s) (by
    intro W V g t
    apply ConcreteCategory.hom_ext
    intro a
    exact sectionFunctions_map A i g a (pointOfNeighborhood s t))

private theorem stalkEvaluation_germ (W : X.Etale) (t : (Φ s).fiber.obj W)
    (a : ↥((P i A).obj (op W))) :
    stalkEvaluation i A s ((Φ s).toPresheafFiber W t (P i A) a) =
      (sectionFunctions A i W a).val (pointOfNeighborhood s t) := by
  have he : (Φ s).toPresheafFiber W t (P i A) ≫ stalkEvaluation i A s = sectionEvaluation i A s W t :=
    (Φ s).toPresheafFiber_presheafFiberDesc _ _ W t
  exact ConcreteCategory.congr_hom he a

private theorem stalkEvaluation_injective : Function.Injective (stalkEvaluation i A s) := by
  intro a b h
  obtain ⟨W, t, a', b', rfl, rfl⟩ := (Φ s).toPresheafFiber_jointly_surjective₂ a b
  rw [stalkEvaluation_germ, stalkEvaluation_germ] at h
  exact ((Φ s).toPresheafFiber_eq_iff' W t a' b').mpr
    (exists_refinement_of_same_value i A s t a' b' h)

private theorem stalkEvaluation_surjective [IsClosedImmersion i] (hs : s default ∉ Set.range i) :
    Function.Surjective (stalkEvaluation i A s) := by
  intro a
  let U : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : Set.range s ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z default, Scheme.Opens.range_ι]
    exact hs
  let W := Scheme.Etale.mk U.ι
  let t : (Φ s).fiber.obj W := Over.homMk (IsOpenImmersion.lift U.ι s hU)
    (IsOpenImmersion.lift_fac U.ι s hU)
  let f : PhilipponEtaleProperRelativeMaps.vanishingFunctions A (pullback.fst W.hom i) :=
    ⟨ContinuousMap.const _ a, fun z => by
      have hr : pullback.fst W.hom i z ∈ Set.range (pullback.fst W.hom i) := Set.mem_range_self z
      rw [Scheme.Pullback.range_fst] at hr
      exact False.elim ((pullback.fst W.hom i z).property hr)⟩
  refine ⟨(Φ s).toPresheafFiber W t (P i A) ((sectionFunctions A i W).symm f), ?_⟩
  rw [stalkEvaluation_germ, AddEquiv.apply_symm_apply]
  rfl

end Sections

/-- At a geometric point of the complementary open, evaluation identifies
the stalk of the relative constant sheaf with its coefficient group. -/
def relativeStalkIso_of_not_mem_range {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (A : Type u) [AddCommGroup A] {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s default ∉ Set.range i) :
    (Scheme.pointSmallEtale s).sheafFiber.obj (relativeConstant i A) ≅ AddCommGrpCat.of A := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact (AddEquiv.ofBijective (stalkEvaluation i A s).hom
    ⟨stalkEvaluation_injective i A s, stalkEvaluation_surjective i A s hs⟩).toAddCommGrpIso

/-- The stalk of the relative constant sheaf is zero at a geometric point
in the image of the closed subscheme. -/
theorem isZero_relativeStalk_of_mem_range {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : Type u) [AddCommGroup A] {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s default ∈ Set.range i) :
    IsZero ((Scheme.pointSmallEtale s).sheafFiber.obj (relativeConstant i A)) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  change IsZero ((Φ s).presheafFiber.obj (P i A))
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  suffices hzero : ∀ p : ↥((Φ s).presheafFiber.obj (P i A)), p = 0 from
    ⟨fun p q => (hzero p).trans (hzero q).symm⟩
  intro p
  obtain ⟨W, t, a, rfl⟩ := (Φ s).toPresheafFiber_jointly_surjective p
  have ht : W.hom (pointOfNeighborhood s t) = s default :=
    (Scheme.pointSmallEtaleFiberObjToPreimage s rfl t).property
  have hx : pointOfNeighborhood s t ∈ Set.range (pullback.fst W.hom i) := by
    rw [Scheme.Pullback.range_fst]
    change W.hom (pointOfNeighborhood s t) ∈ Set.range i
    rwa [ht]
  obtain ⟨z, hz⟩ := hx
  apply stalkEvaluation_injective i A s
  rw [stalkEvaluation_germ, map_zero]
  exact hz ▸ (sectionFunctions A i W a).property z

/-- Relative constants restrict to zero along any morphism whose image
is contained in the center. -/
theorem isZero_pullback_relativeConstant_of_range_subset {X Z V : Scheme.{u}} (g : V ⟶ X)
    (i : Z ⟶ X) (A : Type u) [AddCommGroup A] (h : Set.range g ⊆ Set.range i) :
    IsZero ((PhilipponEtaleSmallSite.pullbackSheaves g).obj (relativeConstant i A)) := by
  apply PhilipponEtaleGeometricStalks.isZero_of_stalks
  intro y
  let s := PhilipponEtaleGeometricStalks.geometricMap y
  let e := (PhilipponEtaleStalkPullback.stalkPullbackIso g s).app (relativeConstant i A)
  refine IsZero.of_iso ?_ e
  exact isZero_relativeStalk_of_mem_range i A (s ≫ g) (h ⟨s default, rfl⟩)

end PhilipponEtaleRelativeStalks

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
namespace PhilipponEtaleBaseChangeMap
universe u
section IsomorphicPoint

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X) [IsIso s]

private abbrev T (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)
private abbrev Φ := Scheme.pointSmallEtale s

private def terminalPoint : (Φ s).fiber.obj (T X) := Over.homMk s (Category.comp_id _)

private def initialNeighborhood : IsInitial ((Φ s).fiber.elementsMk (T X) (terminalPoint s)) := by
  refine IsInitial.ofUniqueHom (fun W => ?_) (fun W h => ?_)
  · let g : T X ⟶ W.fst := MorphismProperty.Over.homMk (inv s ≫ W.snd.left) (by
      have hw : W.snd.left ≫ W.fst.hom = s := Over.w W.snd
      change (inv s ≫ W.snd.left) ≫ W.fst.hom = 𝟙 X
      rw [Category.assoc, hw, IsIso.inv_hom_id]) trivial
    refine ⟨g, Over.OverMorphism.ext ?_⟩
    change s ≫ inv s ≫ W.snd.left = W.snd.left
    exact IsIso.hom_inv_id_assoc _ _
  · apply Subtype.ext
    apply MorphismProperty.Comma.Hom.ext
    · have w := congrArg Over.Hom.left h.property
      change s ≫ h.val.left = W.snd.left at w
      change h.val.left = inv s ≫ W.snd.left
      apply (cancel_epi s).mp
      rw [w, IsIso.hom_inv_id_assoc]
    · exact Subsingleton.elim _ _

/-- A geometric point that is an isomorphism has stalk functor given by
evaluation at the terminal étale object. -/
def pointStalkIsoOfIsIso : (Φ s).sheafFiber ≅ globalSections X := by
  let J := X.smallEtaleTopology
  let A := AddCommGrpCat.{u}
  let α := Functor.whiskerLeft (sheafToPresheaf J A)
    ((Φ s).toPresheafFiberNatTrans (T X) (terminalPoint s))
  have h (F : Sheaf J A) : IsIso (α.app F) := by
    let D := (CategoryOfElements.π (Φ s).fiber).op ⋙ F.obj
    change IsIso (colimit.ι D (op ((Φ s).fiber.elementsMk (T X) (terminalPoint s))))
    exact (colimit.isColimit D).isIso_ι_app_of_isTerminal _ (initialNeighborhood s).op
  letI : IsIso α := NatIso.isIso_of_isIso_app _
  exact (asIso α).symm

end IsomorphicPoint
end PhilipponEtaleBaseChangeMap

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeMap (pointStalkIsoOfIsIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleProperRelativeMaps (isIso_geometricFiber_of_mem range_snd_subset_exceptional)
open PhilipponEtaleRelativeCohomology (relativeConstant)
open PhilipponEtaleRelativeDirectImage (relativeConstantDirectImageIso)
open PhilipponEtaleRelativeStalks (relativeStalkIso_of_not_mem_range isZero_relativeStalk_of_mem_range
  isZero_pullback_relativeConstant_of_range_subset)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleGeometricExcisionZero

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
  (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)
  (A : Type u) [AddCommGroup A] {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X)

private abbrev rel := relativeConstant (pullback.fst f i) A

private def ordinaryExcisionIso :
    (Scheme.pointSmallEtale s).sheafFiber.obj ((pushforward f).obj (rel f i A)) ≅
      (globalSections (pullback s f)).obj ((pullbackSheaves (pullback.snd s f)).obj (rel f i A)) := by
  let Φ := Scheme.pointSmallEtale s
  let R := rel f i A
  let p := pullback.snd s f
  let D := (pullbackSheaves p).obj R
  let e := Φ.sheafFiber.mapIso (relativeConstantDirectImageIso A f i U hU).symm
  by_cases hs : s default ∈ Set.range i
  · have hall : Set.range s ⊆ Set.range i := by
      rintro _ ⟨x, rfl⟩
      rwa [Subsingleton.elim x default]
    have hD : IsZero D := isZero_pullback_relativeConstant_of_range_subset p _ A
      (range_snd_subset_exceptional f i s hall)
    exact e ≪≫ (isZero_relativeStalk_of_mem_range i A s hs).iso ((globalSections _).map_isZero hD)
  · have hu : s default ∈ U := by
      change s default ∈ (U : Set X)
      simpa only [hU, Set.mem_compl_iff, not_not] using hs
    have : IsIso (pullback.fst s f) := isIso_geometricFiber_of_mem f U s hu
    let t : Spec (CommRingCat.of K) ⟶ pullback s f := inv (pullback.fst s f)
    have : IsIso t := inferInstanceAs (IsIso (inv (pullback.fst s f)))
    have hcomp : (t ≫ p) ≫ f = s := by
      change (inv (pullback.fst s f) ≫ pullback.snd s f) ≫ f = s
      rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
    have ht : (t ≫ p) default ∉ Set.range (pullback.fst f i) := by
      rw [Scheme.Pullback.range_fst]
      change f ((t ≫ p) default) ∉ Set.range i
      rwa [← Scheme.Hom.comp_apply, hcomp]
    exact e ≪≫ relativeStalkIso_of_not_mem_range i A s hs ≪≫
      (relativeStalkIso_of_not_mem_range (pullback.fst f i) A (t ≫ p) ht).symm ≪≫
      (stalkPullbackIso p t).symm.app R ≪≫ (pointStalkIsoOfIsIso t).app D

/-- The degree-zero geometric comparison for relative constants under
proper excision, with the inverse image specified by its adjunction. -/
def geometricExcisionZeroIso
    (L : Ab Y ⥤ Ab (pullback s f)) (adj : L ⊣ pushforward (pullback.snd s f)) :
    (Scheme.pointSmallEtale s).sheafFiber.obj (((pushforward f).rightDerived 0).obj (rel f i A)) ≅
      AddCommGrpCat.of ((L.obj (rel f i A)).H 0) := by
  let R := rel f i A
  let W := pullback s f
  let Φ := Scheme.pointSmallEtale s
  let Γ := globalSections W
  let e := ((pullbackAdjunction (pullback.snd s f)).leftAdjointUniq adj).app R
  let T : W.Etale := Scheme.Etale.mk (𝟙 W)
  let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget W) _ Over.mkIdTerminal
  exact Φ.sheafFiber.mapIso ((pushforward f).rightDerivedZeroIsoSelf.app R) ≪≫
    ordinaryExcisionIso f i U hU A s ≪≫ Γ.mapIso e ≪≫
    (Sheaf.H.equiv₀ (L.obj R) hT).symm.toAddCommGrpIso

end PhilipponEtaleGeometricExcisionZero

end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (A : Type u) [AddCommGroup A] {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Set.range i = (U : Set X)ᶜ)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (L : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (pullback s f).smallEtaleTopology AddCommGrpCat.{u})
    (adj : L ⊣ PhilipponEtaleClosedPushforward.pushforward (pullback.snd s f)) :
    Nonempty ((Scheme.pointSmallEtale s).sheafFiber.obj
      (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived 0).obj (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A)) ≅
      AddCommGrpCat.of ((L.obj (PhilipponEtaleRelativeCohomology.relativeConstant (pullback.fst f i) A)).H 0)) := by
  exact ⟨PhilipponEtaleGeometricExcisionZero.geometricExcisionZeroIso f i U hU A s L adj⟩


end
