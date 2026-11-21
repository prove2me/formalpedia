-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSites
-- name    : AlgebraicGeometry_EtaleStrictLocalSites
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T02:56:38.114177+00:00
-- url     : https://prove2.me/theorems/4cbe94e2-120b-415c-b64d-b9c87feff905
-- title:
--   Small étale sites and strict henselizations
-- statement:
--   Construction of the strict henselization at a geometric point, its affine étale neighborhood presentation, and the behavior of relative constants at geometric stalks.

import Definitions.Def_AlgebraicGeometry_SmallEtaleRelativeConstant
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.VanKampen
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Hypercover.One
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

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

/-- Ext computed by homotopy classes into the extension of an injective
resolution to a cochain complex indexed by the integers. -/
def extViaExtendedResolution {E : Type*} [Category* E] [Abelian E] [HasExt.{w} E]
    {F : E} (I : InjectiveResolution F) (P : E) (q : ℕ) :
    Ext P F q ≃+ ((HomotopyCategory.quotient E _).obj ((CochainComplex.singleFunctor E 0).obj P) ⟶
      (HomotopyCategory.quotient E _).obj ((I.cocomplex.extend natEmbedding)⟦(q : ℤ)⟧)) := by
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
  let shiftD := shiftFunctor (DerivedCategory E) (q : ℤ)
  let eP := (DerivedCategory.singleFunctorIsoCompQ E 0).app P ≪≫
    (DerivedCategory.quotientCompQhIso E).symm.app K
  let eF := (DerivedCategory.singleFunctorIsoCompQ E 0).app F ≪≫
    asIso (DerivedCategory.Q.map a) ≪≫ (DerivedCategory.quotientCompQhIso E).symm.app J
  let eShift := (DerivedCategory.Qh.commShiftIso (q : ℤ)).app (Q.obj J)
  let eQ := (Q.commShiftIso (q : ℤ)).app J
  let e₁ : Ext P F q ≃+ _ := Ext.homAddEquiv.trans
    (homEquivOfIsos eP (shiftD.mapIso eF ≪≫ eShift.symm ≪≫ DerivedCategory.Qh.mapIso eQ.symm))
  have : CochainComplex.IsKInjective (J⟦(q : ℤ)⟧) :=
    (CochainComplex.isKInjective_shift_iff J _).mpr inferInstance
  let e₂ := mapHomEquiv DerivedCategory.Qh
    (A := Q.obj K) (B := Q.obj (J⟦(q : ℤ)⟧)) (CochainComplex.IsKInjective.Qh_map_bijective _ _)
  exact e₁.trans e₂.symm

private def extViaResolution {E : Type*} [Category* E] [Abelian E] [HasExt.{w} E]
    {F : E} (I : InjectiveResolution F) (P : E) (q : ℕ) :
    Ext P F q ≃+ ((HomotopyCategory.quotient E _).obj ((single E (ComplexShape.up ℕ) q).obj P) ⟶
      (HomotopyCategory.quotient E _).obj I.cocomplex) := by
  let Q := HomotopyCategory.quotient E (ComplexShape.up ℤ)
  let J := I.cocomplex.extend natEmbedding
  let K := (CochainComplex.singleFunctor E 0).obj P
  let shiftH := shiftFunctor (HomotopyCategory E (ComplexShape.up ℤ)) (q : ℤ)
  let eq := (HomotopyCategory.singleFunctors E).shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)
  let eSingle := Q.mapIso (extendSingleIso natEmbedding P q (q : ℤ) rfl)
  let eSource := shiftH.mapIso eSingle ≪≫ eq.app P
  let e₃ := homEquivOfIsos (Iso.refl (Q.obj K)) ((Q.commShiftIso (q : ℤ)).app J)
  let extend := natEmbedding.extendHomotopyFunctor E
  let e₄ := mapHomEquiv extend
    (A := (HomotopyCategory.quotient E _).obj ((single E (ComplexShape.up ℕ) q).obj P))
    (B := (HomotopyCategory.quotient E _).obj I.cocomplex)
    ⟨extend.map_injective, extend.map_surjective⟩
  let e₅ := mapHomEquiv shiftH
    (A := Q.obj (((single E (ComplexShape.up ℕ) q).obj P).extend natEmbedding))
    (B := Q.obj J) ⟨shiftH.map_injective, shiftH.map_surjective⟩
  exact (extViaExtendedResolution I P q).trans (e₃.trans
    ((homEquivOfIsos eSource.symm (Iso.refl _)).trans (e₅.symm.trans e₄.symm)))

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

/-- Evaluation at the terminal object of the small étale site. -/
abbrev globalSections (X : Scheme.{u}) :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj (op (terminal X))

/-- The direct image has the same global sections as the original sheaf. -/
def globalSectionsIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeComparison (baseChange baseChange_isContinuous)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtaleBaseChangeMap

universe u

/-- Direct images on small étale sites compose. -/
def pushforwardCompIso {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    pushforward g ⋙ pushforward f ≅ pushforward (g ≫ f) := by
  haveI := baseChange_isContinuous f
  haveI := baseChange_isContinuous g
  haveI := baseChange_isContinuous (g ≫ f)
  exact Functor.sheafPushforwardContinuousComp' (F := baseChange f) (G := baseChange g)
    (FG := baseChange (g ≫ f)) (MorphismProperty.Over.pullbackComp g f).symm
    AddCommGrpCat.{u} X.smallEtaleTopology Y.smallEtaleTopology Z.smallEtaleTopology

/-- The ordinary base-change map, formed from the inverse and direct image
adjunctions and the two compositions of direct images in the square. -/
def baseChangeNatTrans {X Y S : Scheme.{u}} (f : Y ⟶ X) (s : S ⟶ X) :
    pushforward f ⋙ pullbackSheaves s ⟶
      pullbackSheaves (pullback.snd s f) ⋙ pushforward (pullback.fst s f) := by
  let p := pullback.snd s f
  let r := pullback.fst s f
  let e := pushforwardCompIso f p ≪≫ eqToIso (congrArg pushforward (pullback.condition (f := s) (g := f)).symm) ≪≫
    (pushforwardCompIso s r).symm
  exact (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (pullbackAdjunction p).unit _ ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ (Functor.associator _ _ _).inv ≫
    Functor.whiskerLeft _ (Functor.whiskerRight e.hom _) ≫
    Functor.whiskerLeft _ ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (pullbackAdjunction s).counit ≫ (Functor.rightUnitor _).hom)

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

/-- The geometric stalk at the identity point of a separably closed
field is given by evaluation at the terminal étale object. -/
abbrev identityStalkIso (K : Type u) [Field K] [IsSepClosed K] :
    (Scheme.pointSmallEtale (𝟙 (Spec (CommRingCat.of K)))).sheafFiber ≅
      globalSections (Spec (CommRingCat.of K)) :=
  pointStalkIsoOfIsIso (𝟙 _)

/-- The degree-zero geometric base-change map from the stalk of the direct
image to global sections on the geometric fiber. -/
def stalkToFiberSections {X Y : Scheme.{u}} (f : Y ⟶ X)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X) :
    pushforward f ⋙ (Scheme.pointSmallEtale s).sheafFiber ⟶
      pullbackSheaves (pullback.snd s f) ⋙ globalSections (pullback s f) := by
  let S := Spec (CommRingCat.of K)
  let p := pullback.snd s f
  let r := pullback.fst s f
  let e := PhilipponEtaleStalkPullback.stalkPullbackIso s (𝟙 S)
  let d := eqToIso (congrArg (fun t : S ⟶ X => (Scheme.pointSmallEtale t).sheafFiber
    (A := AddCommGrpCat.{u})) (Category.id_comp s).symm)
  exact Functor.whiskerLeft _ (d.hom ≫ e.inv ≫ Functor.whiskerLeft _ (identityStalkIso K).hom) ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (baseChangeNatTrans f s) _ ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (pullbackSheaves p) (globalSectionsIso r).hom

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private instance {X : Scheme.{u}} (Φ : X.smallEtaleTopology.Point.{u}) :
    (Φ.sheafFiber (A := AddCommGrpCat.{u})).Additive :=
  Functor.additive_of_preserves_binary_products _

private instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullbackSheaves f).Additive :=
  (pullbackAdjunction f).left_adjoint_additive

private instance (X : Scheme.{u}) : (globalSections X).Additive where
  map_add := rfl

/-- Exactness of the geometric stalk functor lets it commute with taking
cohomology of the direct image of an injective resolution. -/
def stalkOfHigherImageIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Φ : X.smallEtaleTopology.Point.{u}) (F : Ab Y) (q : ℕ) :
    Φ.sheafFiber.obj (((pushforward f).rightDerived q).obj F) ≅
      ((pushforward f ⋙ Φ.sheafFiber).rightDerived q).obj F := by
  let G := Φ.sheafFiber (A := AddCommGrpCat.{u})
  let I := injectiveResolution F
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  refine G.mapIso (I.isoRightDerivedObj (pushforward f) q) ≪≫ ?_ ≪≫
    (I.isoRightDerivedObj (pushforward f ⋙ G) q).symm
  exact ((K.sc q).mapHomologyIso G).symm

/-- The map obtained by deriving the geometric base-change comparison on
sections. The target is the right derived functor of sections after inverse image. -/
def derivedStalkToFiberSections {X Y : Scheme.{u}} (f : Y ⟶ X)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (F : Ab Y) (q : ℕ) :
    (Scheme.pointSmallEtale s).sheafFiber.obj (((pushforward f).rightDerived q).obj F) ⟶
      ((pullbackSheaves (pullback.snd s f) ⋙ globalSections (pullback s f)).rightDerived q).obj F :=
  (stalkOfHigherImageIso f (Scheme.pointSmallEtale s) F q).hom ≫
    (NatTrans.rightDerived (stalkToFiberSections f s) q).app F

end PhilipponEtaleBaseChangeMap

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

end PhilipponEtaleRelativeDirectImage

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

open AlgebraicGeometry CategoryTheory Opposite


namespace PhilipponEtaleLocalRing

universe u

/-- The ring presheaf sending an étale scheme to its global sections. -/
def sections (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X)

/-- The ring of germs of functions on pointed étale neighborhoods. -/
abbrev stalkRing : CommRingCat.{u} :=
  (Scheme.pointSmallEtale s).presheafFiber.obj (sections X)

/-- Evaluation of a section along a geometric point of its domain. -/
def evaluate (W : X.Etale) (t : (Scheme.pointSmallEtale s).fiber.obj W) :
    (sections X).obj (op W) ⟶ CommRingCat.of K :=
  (show Spec (CommRingCat.of K) ⟶ W.left from t.left).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom

/-- The morphism to the affinization of a neighborhood induced by its geometric point. -/
theorem point_toSpecΓ (W : X.Etale) (t : (Scheme.pointSmallEtale s).fiber.obj W) :
    (show Spec (CommRingCat.of K) ⟶ W.left from t.left) ≫ W.left.toSpecΓ =
      Spec.map (evaluate s W t) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  rfl

/-- Evaluation at the geometric point descends to the ring of germs. -/
def evaluateGerm : stalkRing s ⟶ CommRingCat.of K :=
  (Scheme.pointSmallEtale s).presheafFiberDesc (evaluate s) (by
    intro W V g t
    change g.left.appTop ≫ t.left.appTop ≫ _ = (t.left ≫ g.left).appTop ≫ _
    rw [Scheme.Hom.comp_appTop, Category.assoc])

@[reassoc (attr := simp)]
theorem germ_evaluateGerm (W : X.Etale) (t : (Scheme.pointSmallEtale s).fiber.obj W) :
    (Scheme.pointSmallEtale s).toPresheafFiber W t (sections X) ≫ evaluateGerm s =
      evaluate s W t :=
  (Scheme.pointSmallEtale s).toPresheafFiber_presheafFiberDesc _ _ W t

@[simp] theorem evaluateGerm_germ (W : X.Etale)
    (t : (Scheme.pointSmallEtale s).fiber.obj W) (a : (sections X).obj (op W)) :
    evaluateGerm s ((Scheme.pointSmallEtale s).toPresheafFiber W t (sections X) a) =
      evaluate s W t a :=
  ConcreteCategory.congr_hom (germ_evaluateGerm s W t) a

/-- Nonzero evaluation characterizes the units of the étale stalk. -/
theorem isUnit_iff_evaluateGerm_ne_zero (a : stalkRing s) :
    IsUnit a ↔ evaluateGerm s a ≠ 0 := by
  refine ⟨fun h => (h.map (evaluateGerm s).hom).ne_zero, ?_⟩
  let Φ := Scheme.pointSmallEtale s
  obtain ⟨W, t, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective a
  rw [evaluateGerm_germ]
  intro ha
  let D := W.left.basicOpen a
  let tLeft : Spec (CommRingCat.of K) ⟶ W.left := t.left
  have hD : Set.range tLeft ⊆ Set.range D.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change z ∈ tLeft ⁻¹ᵁ W.left.basicOpen a
    rw [Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine']
    have h : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (tLeft.appTop a)) :=
      isUnit_iff_ne_zero.mpr ha
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr (Ideal.notMem_of_isUnit _ h)
  let V := Scheme.Etale.mk (D.ι ≫ W.hom)
  let g : V ⟶ W := MorphismProperty.Over.homMk D.ι rfl trivial
  let t' : Φ.fiber.obj V := Over.homMk (IsOpenImmersion.lift D.ι tLeft hD) (by
    change IsOpenImmersion.lift D.ι tLeft hD ≫ D.ι ≫ W.hom = s
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w t)
  have ht : Φ.fiber.map g t' = t := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hu : IsUnit ((sections X).map g.op a) := by
    change IsUnit (D.ι.appTop a)
    apply RingedSpace.isUnit_of_isUnit_germ D.toScheme.toRingedSpace
    intro z hz
    apply (D.toScheme.mem_basicOpen_top _ _).mp
    rw [← Scheme.preimage_basicOpen_top]
    exact z.property
  rw [← ht, ← Φ.toPresheafFiber_w_apply g t' (sections X)]
  exact hu.map (Φ.toPresheafFiber V t' (sections X)).hom

instance : IsLocalRing (stalkRing s) := by
  let : Nontrivial (stalkRing s) := (evaluateGerm s).hom.domain_nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases ha : evaluateGerm s a = 0
  · right
    rw [isUnit_iff_evaluateGerm_ne_zero, map_sub, map_one, ha, sub_zero]
    exact one_ne_zero
  · exact Or.inl ((isUnit_iff_evaluateGerm_ne_zero s a).mpr ha)

instance : IsLocalHom (evaluateGerm s).hom where
  map_nonunit a h := (isUnit_iff_evaluateGerm_ne_zero s a).mpr h.ne_zero

/-- The image of evaluation realizes the residue field as a subfield of the field
of the geometric point. -/
theorem ker_evaluateGerm : RingHom.ker (evaluateGerm s).hom = IsLocalRing.maximalIdeal (stalkRing s) := by
  ext a
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_evaluateGerm_ne_zero, not_ne_iff]

end PhilipponEtaleLocalRing

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial
open PhilipponEtaleLocalRing


namespace PhilipponEtaleHenselianStalk

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X)

private abbrev point := Scheme.pointSmallEtale s

private abbrev germ (W : X.Etale) (t : (point s).fiber.obj W) :=
  (point s).toPresheafFiber W t (sections X)

/-- A finite family of germs can be represented on a single pointed neighborhood. -/
private theorem exists_representatives {ι : Type*} [Fintype ι] (a : ι → stalkRing s) :
    ∃ (W : X.Etale) (t : (point s).fiber.obj W) (b : ι → (sections X).obj (op W)),
      ∀ i, germ s W t (b i) = a i := by
  classical
  choose W t b h using fun i => (point s).toPresheafFiber_jointly_surjective (a i)
  let V (i : ι) : (point s).fiber.Elements := ⟨W i, t i⟩
  obtain ⟨Z, hZ⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image V)
  let f (i : ι) : Z ⟶ V i := (hZ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).some
  refine ⟨Z.1, Z.2, fun i => (sections X).map (f i).val.op (b i), ?_⟩
  intro i
  rw [(point s).toPresheafFiber_w_apply]
  exact (congrArg (fun z => germ s (W i) z (b i)) (f i).property).trans (h i)

/-- The standard étale algebra inverting the derivative provides a neighborhood
on which the residue root extends to a section. -/
private theorem exists_root_germ {W : X.Etale} (t : (point s).fiber.obj W)
    (p : ((sections X).obj (op W))[X]) (hp : p.Monic) (a : K)
    (ha : p.eval₂ (evaluate s W t).hom a = 0)
    (hder : p.derivative.eval₂ (evaluate s W t).hom a ≠ 0) :
    ∃ b : stalkRing s, p.eval₂ (germ s W t).hom b = 0 ∧ evaluateGerm s b = a := by
  let R := (sections X).obj (op W)
  let P : StandardEtalePair R := ⟨p, hp, p.derivative, 1, 0, 1,
    by rw [mul_one, mul_zero, add_zero, pow_one]⟩
  let C := CommRingCat.of P.Ring
  let e : R ⟶ C := CommRingCat.ofHom (algebraMap R P.Ring)
  let : Algebra R K := (evaluate s W t).hom.toAlgebra
  have hP : P.HasMap a := ⟨ha, isUnit_iff_ne_zero.mpr hder⟩
  let r : C ⟶ CommRingCat.of K := CommRingCat.ofHom (P.lift a hP).toRingHom
  have her : e ≫ r = evaluate s W t := by
    apply ConcreteCategory.hom_ext
    intro z
    exact (P.lift a hP).commutes z
  have he : Etale (Spec.map e) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let u := W.left.toSpecΓ
  let T := pullback u (Spec.map e)
  let v : T ⟶ W.left := pullback.fst _ _
  let k : T ⟶ Spec C := pullback.snd _ _
  let V : X.Etale := Scheme.Etale.mk (v ≫ W.hom)
  let g : V ⟶ W := MorphismProperty.Over.homMk v rfl trivial
  let tLeft : Spec (CommRingCat.of K) ⟶ W.left := t.left
  have hSquare : tLeft ≫ u = Spec.map r ≫ Spec.map e := by
    rw [← Spec.map_comp, her]
    exact point_toSpecΓ s W t
  let l : Spec (CommRingCat.of K) ⟶ T := pullback.lift tLeft (Spec.map r) hSquare
  have hlv : l ≫ v = tLeft := pullback.lift_fst _ _ _
  have hlk : l ≫ k = Spec.map r := pullback.lift_snd _ _ _
  let t' : (point s).fiber.obj V := Over.homMk l (by
    change l ≫ v ≫ W.hom = s
    rw [← Category.assoc, hlv]
    exact Over.w t)
  have ht' : (point s).fiber.map g t' = t := Over.OverMorphism.ext hlv
  let θ : C ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso C).inv ≫ k.appTop
  have hv : v.appTop = e ≫ θ := by
    have h := congrArg (fun m : T ⟶ Spec R => m.appTop)
      (pullback.condition (f := u) (g := Spec.map e))
    change (v ≫ u).appTop = (k ≫ Spec.map e).appTop at h
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, u] at h
    change (Scheme.ΓSpecIso R).hom ≫ v.appTop = (Spec.map e).appTop ≫ k.appTop at h
    calc
      v.appTop = (Scheme.ΓSpecIso R).inv ≫ (Scheme.ΓSpecIso R).hom ≫ v.appTop := by simp
      _ = e ≫ θ := by rw [h, Scheme.ΓSpecIso_inv_naturality_assoc]
  let β : C ⟶ stalkRing s := θ ≫ germ s V t'
  have hβ : e ≫ β = germ s W t := by
    change e ≫ θ ≫ germ s V t' = germ s W t
    rw [← Category.assoc, ← hv]
    change (sections X).map g.op ≫ germ s V t' = germ s W t
    rw [(point s).toPresheafFiber_w, ht']
  have hβr : β ≫ evaluateGerm s = r := by
    change (θ ≫ germ s V t') ≫ evaluateGerm s = r
    rw [Category.assoc, germ_evaluateGerm s V t']
    change ((Scheme.ΓSpecIso C).inv ≫ k.appTop) ≫
      l.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom = r
    rw [Category.assoc, ← Scheme.Hom.comp_appTop_assoc, hlk,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  refine ⟨β P.X, ?_, ?_⟩
  · have hroot : p.eval₂ e.hom P.X = 0 := (StandardEtalePair.hasMap_X (P := P)).1
    rw [← hβ, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, hroot, map_zero]
  · exact (ConcreteCategory.congr_hom hβr P.X).trans (P.lift_X a hP)

/-- A simple root in the field of the geometric point lifts to an étale germ. -/
theorem exists_lift_root {p : (stalkRing s)[X]} (hp : p.Monic) (a : K)
    (ha : p.eval₂ (evaluateGerm s).hom a = 0)
    (hder : p.derivative.eval₂ (evaluateGerm s).hom a ≠ 0) :
    ∃ b : stalkRing s, p.IsRoot b ∧ evaluateGerm s b = a := by
  obtain ⟨W, t, b, hb⟩ := exists_representatives s (fun i : p.support => p.coeff i)
  have hlifts : p ∈ Polynomial.lifts (germ s W t).hom := by
    apply (Polynomial.lifts_iff_coeff_lifts p).mpr
    intro i
    by_cases hi : i ∈ p.support
    · exact ⟨b ⟨i, hi⟩, hb ⟨i, hi⟩⟩
    · exact ⟨0, by rw [map_zero, Polynomial.notMem_support_iff.mp hi]⟩
  obtain ⟨q, rfl, _, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hEval : (evaluateGerm s).hom.comp (germ s W t).hom = (evaluate s W t).hom := by
    ext z
    exact evaluateGerm_germ s W t z
  rw [Polynomial.eval₂_map, hEval] at ha
  rw [Polynomial.derivative_map, Polynomial.eval₂_map, hEval] at hder
  obtain ⟨c, hc, hca⟩ := exists_root_germ s t q hq a ha hder
  exact ⟨c, (Polynomial.eval_map _ _).trans hc, hca⟩

instance henselianLocalRing : HenselianLocalRing (stalkRing s) where
  is_henselian p hp a ha hder := by
    rw [← ker_evaluateGerm, RingHom.mem_ker, ← Polynomial.eval₂_at_apply] at ha
    have h := (isUnit_iff_evaluateGerm_ne_zero s _).mp hder
    rw [← Polynomial.eval₂_at_apply] at h
    obtain ⟨b, hb, hba⟩ := exists_lift_root s hp (evaluateGerm s a) ha h
    refine ⟨b, hb, ?_⟩
    rw [← ker_evaluateGerm, RingHom.mem_ker, map_sub, hba, sub_self]

/-- The residue field of the stalk embeds into the geometric point's field. -/
def residueEmbedding : IsLocalRing.ResidueField (stalkRing s) →+* K :=
  IsLocalRing.ResidueField.lift (evaluateGerm s).hom

/-- A simple root of a residue polynomial in the geometric point's field
already comes from the residue field of the étale stalk. -/
theorem exists_residue_root {p : (IsLocalRing.ResidueField (stalkRing s))[X]}
    (hp : p.Monic) (a : K) (ha : p.eval₂ (residueEmbedding s) a = 0)
    (hder : p.derivative.eval₂ (residueEmbedding s) a ≠ 0) :
    ∃ b : IsLocalRing.ResidueField (stalkRing s),
      p.IsRoot b ∧ residueEmbedding s b = a := by
  let ρ := IsLocalRing.residue (stalkRing s)
  have hlifts : p ∈ Polynomial.lifts ρ :=
    Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective p
  obtain ⟨q, hmap, _, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hcomp : (residueEmbedding s).comp ρ = (evaluateGerm s).hom :=
    IsLocalRing.ResidueField.lift_comp_residue _
  rw [← hmap, Polynomial.eval₂_map, hcomp] at ha
  rw [← hmap, Polynomial.derivative_map, Polynomial.eval₂_map, hcomp] at hder
  obtain ⟨b, hb, hba⟩ := exists_lift_root s hq a ha hder
  refine ⟨ρ b, ?_, hba⟩
  rw [← hmap, Polynomial.IsRoot.def, Polynomial.eval_map_apply, hb, map_zero]

instance residueFieldIsSepClosed : IsSepClosed (IsLocalRing.ResidueField (stalkRing s)) := by
  apply IsSepClosed.of_exists_root
  intro p hp hirr hsep
  obtain ⟨a, ha⟩ := IsSepClosed.exists_eval₂_eq_zero (residueEmbedding s) p
    (Polynomial.degree_pos_of_irreducible hirr).ne' hsep
  obtain ⟨b, hb, _⟩ := exists_residue_root s hp a ha
    (hsep.eval₂_derivative_ne_zero (residueEmbedding s) ha)
  exact ⟨b, hb⟩

end PhilipponEtaleHenselianStalk

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleLocalRing PhilipponEtaleHenselianStalk


namespace PhilipponEtaleStrictHenselization

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X)

/-- Pointed étale neighborhoods of a geometric point. -/
abbrev Neighborhood := (Scheme.pointSmallEtale s).fiber.Elements

/-- The diagram of underlying schemes of the pointed neighborhoods. -/
abbrev neighborhoods : Neighborhood s ⥤ Scheme.{u} :=
  CategoryOfElements.π (Scheme.pointSmallEtale s).fiber ⋙ Scheme.Etale.forget X ⋙ Over.forget X

/-- The affine pointed neighborhoods form a coinitial full subcategory. -/
def IsAffineNeighborhood : ObjectProperty (Neighborhood s) :=
  fun W => IsAffine W.1.left

abbrev affineInclusion := (IsAffineNeighborhood s).ι

instance affineInclusion_initial : (affineInclusion s).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro W
  let t : Spec (CommRingCat.of K) ⟶ W.1.left := W.2.left
  obtain ⟨j, z, hz⟩ := W.1.left.affineCover.exists_eq (t default)
  let i := W.1.left.affineCover.f j
  have hi : Set.range t ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact ⟨z, (Subsingleton.elim x default).symm ▸ hz⟩
  let V := Scheme.Etale.mk (i ≫ W.1.hom)
  let g : V ⟶ W.1 := MorphismProperty.Over.homMk i rfl trivial
  let l := IsOpenImmersion.lift i t hi
  have hl : l ≫ i = t := IsOpenImmersion.lift_fac ..
  let v : (Scheme.pointSmallEtale s).fiber.obj V := Over.homMk l (by
    change l ≫ i ≫ W.1.hom = s
    rw [← Category.assoc, hl]
    exact Over.w W.2)
  have hV : IsAffine V.left := by
    change IsAffine (W.1.left.affineCover.X j)
    infer_instance
  exact ⟨⟨⟨V, v⟩, hV⟩, ⟨⟨g, Over.OverMorphism.ext hl⟩⟩⟩

instance affineNeighborhoods_cofiltered : IsCofiltered (IsAffineNeighborhood s).FullSubcategory :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful (affineInclusion s) (fun W =>
    ⟨Functor.Initial.lift (affineInclusion s) W, ⟨Functor.Initial.homToLift (affineInclusion s) W⟩⟩)

private abbrev affineDiagram := affineInclusion s ⋙ neighborhoods s

private def affineCocone :=
  ((Scheme.pointSmallEtale s).presheafFiberCocone (sections X)).whisker (affineInclusion s).op

private def affineToSpec :
    affineDiagram s ≅ affineDiagram s ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := by
  let α := (affineDiagram s).whiskerLeft ΓSpec.adjunction.unit
  have (W : (IsAffineNeighborhood s).FullSubcategory) : IsIso (α.app W) := by
    let : IsAffine W.obj.1.left := W.property
    change IsIso W.obj.1.left.toSpecΓ
    exact IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The colimit of section rings on affine neighborhoods gives a limit of schemes. -/
private def affineLimitCone : LimitCone (affineDiagram s) := by
  let h := (Functor.Final.isColimitWhiskerEquiv (affineInclusion s).op _).symm
    ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone (sections X))
  let c := coneRightOpOfCocone (affineCocone s)
  let hc : IsLimit c := isLimitConeRightOpOfCocone _ h
  exact ⟨(Cone.postcompose (affineToSpec s).inv).obj (Scheme.Spec.mapCone c),
    (IsLimit.postcomposeHomEquiv (affineToSpec s).symm _).symm
      (isLimitOfPreserves Scheme.Spec hc)⟩

/-- The spectrum of the étale local ring is the limit of the pointed
étale neighborhoods. -/
def neighborhoodLimitCone : LimitCone (neighborhoods s) :=
  Functor.Initial.limitConeOfComp (affineInclusion s) (affineLimitCone s)

@[simp] theorem neighborhoodLimitCone_pt :
    (neighborhoodLimitCone s).cone.pt = Spec (stalkRing s) := rfl

/-- The geometric point furnished by evaluation gives back the chosen lift
on every étale neighborhood. -/
theorem evaluation_comp_projection (W : Neighborhood s) :
    Spec.map (evaluateGerm s) ≫ (neighborhoodLimitCone s).cone.π.app W = W.2.left := by
  let F := affineInclusion s
  let V := Functor.Initial.lift F W
  let g := Functor.Initial.homToLift F W
  change Spec.map (evaluateGerm s) ≫
    (Functor.Initial.extendCone.obj (affineLimitCone s).cone).π.app W = W.2.left
  rw [Functor.Initial.extendCone_obj_π_app' (affineLimitCone s).cone g, ← Category.assoc]
  have h : Spec.map (evaluateGerm s) ≫ (affineLimitCone s).cone.π.app V = V.obj.2.left := by
    change Spec.map (evaluateGerm s) ≫
      Spec.map ((Scheme.pointSmallEtale s).toPresheafFiber V.obj.1 V.obj.2 (sections X)) ≫
        (affineToSpec s).inv.app V = V.obj.2.left
    rw [← Spec.map_comp_assoc, germ_evaluateGerm, ← point_toSpecΓ, Category.assoc]
    change V.obj.2.left ≫ (affineToSpec s).hom.app V ≫ (affineToSpec s).inv.app V = V.obj.2.left
    rw [Iso.hom_inv_id_app]
    exact Category.comp_id (show Spec (CommRingCat.of K) ⟶ (affineDiagram s).obj V from V.obj.2.left)
  rw [h]
  exact congrArg Over.Hom.left g.property

private abbrev identityNeighborhood : Neighborhood s :=
  ⟨Scheme.Etale.mk (𝟙 X), Over.homMk s (Category.comp_id _)⟩

/-- The morphism from the spectrum of the étale local ring to the original scheme. -/
def toBase : Spec (stalkRing s) ⟶ X :=
  (neighborhoodLimitCone s).cone.π.app (identityNeighborhood s)

theorem evaluation_comp_toBase : Spec.map (evaluateGerm s) ≫ toBase s = s :=
  evaluation_comp_projection s _

theorem projection_comp_hom (W : Neighborhood s) :
    (neighborhoodLimitCone s).cone.π.app W ≫ W.1.hom = toBase s := by
  let f : W.1 ⟶ (identityNeighborhood s).1 :=
    MorphismProperty.Over.homMk W.1.hom (Category.comp_id _) trivial
  let g : W ⟶ identityNeighborhood s := ⟨f, Over.OverMorphism.ext (Over.w W.2)⟩
  exact (neighborhoodLimitCone s).cone.w g

private def neighborhoodMaps : neighborhoods s ⟶ (Functor.const (Neighborhood s)).obj X where
  app W := W.1.hom
  naturality W V g := by
    change g.val.left ≫ V.1.hom = W.1.hom ≫ 𝟙 X
    exact (MorphismProperty.Over.w g.val).trans (Category.comp_id _).symm

/-- The diagram obtained by pulling each pointed étale neighborhood back along a morphism. -/
abbrev pullbackNeighborhoods {Y : Scheme.{u}} (f : Y ⟶ X) : Neighborhood s ⥤ Scheme.{u} :=
  Over.lift (neighborhoods s) (neighborhoodMaps s) ⋙ Over.pullback f ⋙ Over.forget Y

/-- Pulling back the spectrum of the étale local ring computes the limit of
the pulled-back neighborhoods. -/
def pullbackNeighborhoodLimitCone {Y : Scheme.{u}} (f : Y ⟶ X) :
    LimitCone (pullbackNeighborhoods s f) := by
  let : Nonempty (Neighborhood s) := ⟨identityNeighborhood s⟩
  let : IsConnected (Neighborhood s) := IsCofiltered.isConnected (Neighborhood s)
  let c := neighborhoodLimitCone s
  let hc := Over.isLimitLiftCone (neighborhoods s) (neighborhoodMaps s)
    c.cone (toBase s) (projection_comp_hom s) c.isLimit
  let G := Over.pullback f ⋙ Over.forget Y
  exact ⟨G.mapCone _, isLimitOfPreserves G hc⟩

@[simp] theorem pullbackNeighborhoodLimitCone_pt {Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackNeighborhoodLimitCone s f).cone.pt = pullback (toBase s) f := rfl

/-- The transition maps between pullbacks of affine neighborhoods are affine. -/
theorem affinePullbackTransition {Y : Scheme.{u}} (f : Y ⟶ X)
    {V W : (IsAffineNeighborhood s).FullSubcategory} (g : V ⟶ W) :
    IsAffineHom ((affineInclusion s ⋙ pullbackNeighborhoods s f).map g) := by
  let a := V.obj.1.hom
  let b := W.obj.1.hom
  let v : V.obj.1.left ⟶ W.obj.1.left := g.hom.val.left
  let k : pullback a f ⟶ pullback b f := (affineInclusion s ⋙ pullbackNeighborhoods s f).map g
  have hv : v ≫ b = a := MorphismProperty.Over.w g.hom.val
  have h₁ : k ≫ pullback.fst b f = pullback.fst a f ≫ v := pullback.lift_fst ..
  have h₂ : k ≫ pullback.snd b f = pullback.snd a f := pullback.lift_snd ..
  have h : IsPullback (pullback.fst a f) (k ≫ pullback.snd b f) (v ≫ b) f := by
    rw [h₂, hv]
    exact IsPullback.of_hasPullback a f
  let : IsAffine V.obj.1.left := V.property
  let : IsAffine W.obj.1.left := W.property
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_bot h h₁.symm (IsPullback.of_hasPullback b f)) (inferInstance : IsAffineHom v)

/-- The map from the closed residue point to the spectrum of the étale local ring. -/
def closedPointInclusion :
    Spec (CommRingCat.of (IsLocalRing.ResidueField (stalkRing s))) ⟶ Spec (stalkRing s) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue (stalkRing s)))

theorem geometricPoint_factors :
    Spec.map (CommRingCat.ofHom (residueEmbedding s)) ≫ closedPointInclusion s ≫ toBase s = s := by
  rw [closedPointInclusion, ← Category.assoc, ← Spec.map_comp]
  exact evaluation_comp_toBase s

theorem closedPoint_maps_to_geometricImage :
    (closedPointInclusion s ≫ toBase s) default = s default := by
  have h := congrArg (fun f : Spec (CommRingCat.of K) ⟶ X => f default)
    (geometricPoint_factors s)
  rw [Scheme.Hom.comp_apply, Subsingleton.elim
    (Spec.map (CommRingCat.ofHom (residueEmbedding s)) default) default] at h
  exact h

theorem closedPoint_range_subset {Z : Scheme.{u}} (i : Z ⟶ X) (hs : s default ∈ Set.range i) :
    Set.range (closedPointInclusion s ≫ toBase s) ⊆ Set.range i := by
  rintro _ ⟨z, rfl⟩
  rw [Subsingleton.elim z default, closedPoint_maps_to_geometricImage]
  exact hs

end PhilipponEtaleStrictHenselization

end

end


