-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_restrict_injective_prime_of_affine_closedImmersion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T22:12:41.346324+00:00
-- url     : https://prove2.me/submissions/12293b79-bc14-49e3-b978-ab6cd83068da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Presheaf
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_of_henselian_pair
import Theorems.Thm_AlgebraicGeometry_Scheme_subsingleton_etale_cohomology_of_affine_limit

set_option maxHeartbeats 1600000

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

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PhilipponSchemeIdempotents

universe u

/-- The characteristic section of a clopen subset is a global idempotent. -/
theorem exists_idempotent_of_clopen (X : Scheme.{u}) {s : Set X} (hs : IsClopen s) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      (∀ x ∈ s, X.presheaf.Γgerm x e = 1) ∧
      (∀ x ∉ s, X.presheaf.Γgerm x e = 0) := by
  classical
  let U : Bool → X.Opens := fun i => if i then ⟨s, hs.2⟩ else ⟨sᶜ, hs.1.isOpen_compl⟩
  let a (i : Bool) : Γ(X, U i) := if i then 1 else 0
  let k (i : Bool) : U i ⟶ ⊤ := homOfLE le_top
  have hDisj : ∀ i j : Bool, i ≠ j → U i ⊓ U j = ⊥ := by
    intro i j hij
    cases i <;> cases j <;> simp_all [U]
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ s
    · exact ⟨true, by simpa [U] using hx⟩
    · exact ⟨false, by simpa [U] using hx⟩
  have hCompatible : TopCat.Presheaf.IsCompatible X.presheaf U a := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · exact (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (hDisj i j hij))).elim _ _
  obtain ⟨e, hRes, hUnique⟩ := X.sheaf.existsUnique_gluing' U ⊤ k hcover a hCompatible
  have hRes' (i : Bool) : (X.presheaf.map (k i).op).hom e = a i := hRes i
  have he : IsIdempotentElem e := by
    change e * e = e
    apply hUnique
    intro i
    let g := (X.presheaf.map (k i).op).hom
    calc
      g (e * e) = g e * g e := map_mul g e e
      _ = a i * a i := congrArg (fun z : Γ(X, U i) => z * z) (hRes' i)
      _ = a i := by cases i <;> simp [a]
  have hg (i : Bool) (x : X) (hx : x ∈ U i) :
      X.presheaf.Γgerm x e = X.presheaf.germ (U i) x hx (a i) := by
    rw [← hRes' i]
    exact (X.presheaf.germ_res_apply (k i) x hx e).symm
  refine ⟨e, he, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ U true := by simpa [U] using hx
    simpa only [a, if_true, map_one] using hg true x hx'
  · intro x hx
    have hx' : x ∈ U false := by simpa [U] using hx
    simpa only [a, Bool.false_eq_true, if_false, map_zero] using hg false x hx'

/-- A scheme whose global functions have only trivial idempotents has
preconnected underlying space. -/
theorem preconnectedSpace_of_trivial_idempotents (X : Scheme.{u})
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) : PreconnectedSpace X := by
  apply preconnectedSpace_iff_clopen.2
  intro s hs
  obtain ⟨e, he, h1, h0⟩ := exists_idempotent_of_clopen X hs
  rcases h e he with he₀ | he₁
  · left
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact zero_ne_one (by simpa only [he₀, map_zero] using h1 x hx)
  · right
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact one_ne_zero (by simpa only [he₁, map_one] using h0 x hx)

end PhilipponSchemeIdempotents

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Polynomial


namespace PhilipponHenselianPairNeighborhoods

universe u

private theorem exists_basicOpen_eq_clopen (W : Scheme.{u}) {S : Set W} (hS : IsClopen S) :
    ∃ e : Γ(W, ⊤), (W.basicOpen e : Set W) = S := by
  obtain ⟨e, _, h₁, h₀⟩ := PhilipponSchemeIdempotents.exists_idempotent_of_clopen W hS
  refine ⟨e, Set.ext (fun x => ?_)⟩
  rw [SetLike.mem_coe, Scheme.mem_basicOpen_top]
  change IsUnit (W.presheaf.Γgerm x e) ↔ x ∈ S
  by_cases hx : x ∈ S
  · rw [h₁ x hx]
    exact ⟨fun _ => hx, fun _ => isUnit_one⟩
  · rw [h₀ x hx]
    exact ⟨fun h => (not_isUnit_zero h).elim, fun h => (hx h).elim⟩

/-- An affine étale neighborhood of a closed subscheme can be shrunk to
an affine open on which the chosen section is the whole closed base change. -/
theorem exists_affine_refinement {X Z U : Scheme.{u}} [IsAffine X] [IsAffine U]
    (i : Z ⟶ X) [IsClosedImmersion i] (g : U ⟶ X) [Etale g]
    (t : Z ⟶ U) (h : t ≫ g = i) :
    ∃ (V : U.Opens) (z : Z ⟶ V.toScheme), IsAffineOpen V ∧
      z ≫ V.ι = t ∧ IsPullback z (𝟙 Z) (V.ι ≫ g) i := by
  let p := pullback.fst g i
  let q := pullback.snd g i
  let b := pullback.lift t (𝟙 Z) (h.trans (Category.id_comp i).symm)
  have hbp : b ≫ p = t := pullback.lift_fst ..
  have hbq : b ≫ q = 𝟙 Z := pullback.lift_snd ..
  let : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.fst g i))
  let : Etale q := inferInstanceAs (Etale (pullback.snd g i))
  let : Etale (b ≫ q) := hbq.symm ▸ inferInstanceAs (Etale (𝟙 Z))
  let : Etale b := Etale.of_comp b q
  let : Mono b := mono_of_mono_fac hbq
  let : IsOpenImmersion b := IsOpenImmersion.of_flat_of_mono b
  let : IsAffine Z := isAffine_of_isAffineHom i
  let : IsAffine (pullback g i) := isAffine_of_isAffineHom p
  let : IsClosedImmersion b := IsClosedImmersion.of_surjective_of_isAffine b (by
    have H : q.appTop ≫ b.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, hbq, Scheme.Hom.id_appTop]
    exact fun x => ⟨q.appTop x, ConcreteCategory.congr_hom H x⟩)
  obtain ⟨e₀, he₀⟩ := exists_basicOpen_eq_clopen (pullback g i)
    ⟨b.isClosedEmbedding.isClosed_range, b.isOpenEmbedding.isOpen_range⟩
  obtain ⟨e, he⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine p).2 e₀
  let V := U.basicOpen e
  have hV : IsAffineOpen V := (isAffineOpen_top U).basicOpen e
  have hpre : p ⁻¹ᵁ V = b.opensRange := by
    rw [Scheme.preimage_basicOpen_top, he]
    exact SetLike.coe_injective he₀
  have ht : Set.range t ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [← hbp, Scheme.Hom.comp_apply, Scheme.Opens.range_ι]
    change b x ∈ p ⁻¹ᵁ V
    rw [hpre]
    exact ⟨x, rfl⟩
  let z := IsOpenImmersion.lift V.ι t ht
  have hz : z ≫ V.ι = t := IsOpenImmersion.lift_fac ..
  have h₁ : IsPullback z b V.ι p :=
    IsOpenImmersion.isPullback z b V.ι p (hbp.trans hz.symm)
      (by rwa [Scheme.Opens.opensRange_ι])
  refine ⟨V, z, hV, hz, ?_⟩
  have h₂ := h₁.paste_vert (IsPullback.of_hasPullback g i)
  rwa [hbq] at h₂

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-- An étale neighborhood together with a lift of the prescribed subscheme. -/
abbrev Pointed := (Scheme.Etale.forget X ⋙ coyoneda.obj (op (Over.mk i))).Elements

def IsAffinePointed : ObjectProperty (Pointed i) := fun W => IsAffine W.1.left

abbrev AffinePointed := (IsAffinePointed i).FullSubcategory

private abbrev ambient (W : AffinePointed i) := W.obj.1.left
private abbrev structureMap (W : AffinePointed i) : ambient i W ⟶ X := W.obj.1.hom
private abbrev point (W : AffinePointed i) : Z ⟶ ambient i W := W.obj.2.left

private theorem point_comp (W : AffinePointed i) : point i W ≫ structureMap i W = i :=
  Over.w W.obj.2

private def mkAffine {Y : Scheme.{u}} [IsAffine Y] (g : Y ⟶ X) [Etale g]
    (t : Z ⟶ Y) (h : t ≫ g = i) : AffinePointed i :=
  ⟨⟨Scheme.Etale.mk g, Over.homMk t h⟩, inferInstanceAs (IsAffine Y)⟩

private def homMk {W V : AffinePointed i} (f : ambient i W ⟶ ambient i V)
    (h : f ≫ structureMap i V = structureMap i W)
    (e : point i W ≫ f = point i V) : W ⟶ V :=
  ⟨⟨MorphismProperty.Over.homMk f h trivial, Over.OverMorphism.ext e⟩⟩

private theorem hom_ext {W V : AffinePointed i} {f g : W ⟶ V}
    (h : f.hom.val.left = g.hom.val.left) : f = g := by
  ext
  exact MorphismProperty.Over.Hom.ext h

instance affinePointed_cofiltered [IsAffine X] : IsCofiltered (AffinePointed i) where
  nonempty := ⟨mkAffine i (𝟙 X) i (Category.comp_id _)⟩
  cone_objs U V := by
    let : IsAffine (ambient i U) := U.property
    let : IsAffine (ambient i V) := V.property
    let g := structureMap i U
    let f := structureMap i V
    let p := pullback.fst g f
    let q := pullback.snd g f
    let z := pullback.lift (point i U) (point i V) ((point_comp i U).trans (point_comp i V).symm)
    have hp : z ≫ p = point i U := pullback.lift_fst ..
    have hq : z ≫ q = point i V := pullback.lift_snd ..
    let W := mkAffine i (p ≫ g) z (Category.assoc _ _ _ |>.symm.trans
      (congrArg (· ≫ g) hp |>.trans (point_comp i U)))
    exact ⟨W, homMk i p rfl hp, homMk i q pullback.condition.symm hq, trivial⟩
  cone_maps {U V} f g := by
    let : IsAffine (ambient i U) := U.property
    let : IsAffine (ambient i V) := V.property
    let h := structureMap i V
    let a := f.hom.val.left
    let b := g.hom.val.left
    let p := pullback.lift a b ((MorphismProperty.Over.w f.hom.val).trans
      (MorphismProperty.Over.w g.hom.val).symm)
    let d := pullback.diagonal h
    have hpa : p ≫ pullback.fst h h = a := pullback.lift_fst ..
    have hpb : p ≫ pullback.snd h h = b := pullback.lift_snd ..
    have hd₁ : d ≫ pullback.fst h h = 𝟙 _ := pullback.diagonal_fst h
    have hd₂ : d ≫ pullback.snd h h = 𝟙 _ := pullback.diagonal_snd h
    have he : point i U ≫ p = point i V ≫ d := by
      apply pullback.hom_ext (f := h) (g := h)
      · rw [Category.assoc, hpa, Category.assoc, hd₁, Category.comp_id]
        exact congrArg Over.Hom.left f.hom.property
      · rw [Category.assoc, hpb, Category.assoc, hd₂, Category.comp_id]
        exact congrArg Over.Hom.left g.hom.property
    let k := pullback.fst p d
    let z := pullback.lift (point i U) (point i V) he
    have hz : z ≫ k = point i U := pullback.lift_fst ..
    let W := mkAffine i (k ≫ structureMap i U) z (by
      rw [← Category.assoc, hz]
      exact point_comp i U)
    refine ⟨W, homMk i k rfl hz, hom_ext i ?_⟩
    have H : k ≫ p = pullback.snd p d ≫ d := pullback.condition
    have H₁ := congrArg (· ≫ pullback.fst h h) H
    have H₂ := congrArg (· ≫ pullback.snd h h) H
    change k ≫ a = k ≫ b
    simp only [Category.assoc, hpa, hpb, hd₁, hd₂, Category.comp_id] at H₁ H₂
    exact H₁.trans H₂.symm

instance affinePointed_initiallySmall [IsAffine X] : InitiallySmall.{u} (AffinePointed i) := by
  let F := Scheme.Etale.forget X ⋙ coyoneda.obj (op (Over.mk i))
  let G := Functor.Elements.precomp (Scheme.AffineEtale.Spec X) F
  let T := (IsAffinePointed i).lift G fun W =>
    inferInstanceAs (IsAffine (Spec W.1.left.unop))
  apply initiallySmall_of_essentiallySmall_weakly_initial_objectProperty T.essImage
  intro W
  let : IsAffine (ambient i W) := W.property
  let e := (ambient i W).isoSpec
  let W₀ := Scheme.AffineEtale.mk (e.inv ≫ structureMap i W)
  let w : ((Scheme.AffineEtale.Spec X) ⋙ F).Elements := ⟨W₀, Over.homMk (point i W ≫ e.hom)
    (by
      change (point i W ≫ e.hom) ≫ e.inv ≫ structureMap i W = i
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact point_comp i W)⟩
  refine ⟨T.obj w, ⟨w, ⟨Iso.refl _⟩⟩, ⟨homMk i e.inv rfl ?_⟩⟩
  change (point i W ≫ e.hom) ≫ e.inv = point i W
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The chosen lift identifies the entire closed base change of the neighborhood. -/
def HasExactFiber : ObjectProperty (AffinePointed i) :=
  fun W => IsPullback (point i W) (𝟙 Z) (structureMap i W) i

abbrev ExactAffinePointed := (HasExactFiber i).FullSubcategory

abbrev exactInclusion : ExactAffinePointed i ⥤ AffinePointed i := (HasExactFiber i).ι

instance exactInclusion_initial [IsAffine X] [IsClosedImmersion i] : (exactInclusion i).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro W
  let : IsAffine (ambient i W) := W.property
  obtain ⟨V, z, hV, hz, hpb⟩ := exists_affine_refinement i (structureMap i W) (point i W) (point_comp i W)
  let : IsAffine V.toScheme := hV
  let T := mkAffine i (V.ι ≫ structureMap i W) z (hpb.w.trans (Category.id_comp i))
  exact ⟨⟨T, hpb⟩, ⟨homMk i V.ι rfl hz⟩⟩

instance exactAffinePointed_cofiltered [IsAffine X] [IsClosedImmersion i] :
    IsCofiltered (ExactAffinePointed i) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful (exactInclusion i) fun V =>
    ⟨Functor.Initial.lift (exactInclusion i) V, ⟨Functor.Initial.homToLift (exactInclusion i) V⟩⟩

instance exactAffinePointed_initiallySmall [IsAffine X] [IsClosedImmersion i] :
    InitiallySmall.{u} (ExactAffinePointed i) := by
  let F := exactInclusion i
  let I := fromInitialModel.{u} (AffinePointed i)
  let chooseExact (n : InitialModel.{u} (AffinePointed i)) := Functor.Initial.lift F (I.obj n)
  apply initiallySmall_of_small_weakly_initial_set (Set.range chooseExact)
  intro V
  obtain ⟨p⟩ : Nonempty (CostructuredArrow I (F.obj V)) := IsConnected.is_nonempty
  exact ⟨chooseExact p.left, Set.mem_range_self _,
    ⟨F.preimage (Functor.Initial.homToLift F (I.obj p.left) ≫ p.hom)⟩⟩

/-- The diagram of underlying schemes of the affine neighborhoods with exact fiber. -/
abbrev schemes : ExactAffinePointed i ⥤ Scheme.{u} :=
  exactInclusion i ⋙ (IsAffinePointed i).ι ⋙
    CategoryOfElements.π (Scheme.Etale.forget X ⋙ coyoneda.obj (op (Over.mk i))) ⋙
    Scheme.Etale.forget X ⋙ Over.forget X

instance isAffine_obj (W : ExactAffinePointed i) : IsAffine ((schemes i).obj W) := W.obj.property

/-- The structure maps of the neighborhoods form a cone to the fixed base. -/
def stagesToBase : schemes i ⟶ (Functor.const (ExactAffinePointed i)).obj X where
  app W := structureMap i W.obj
  naturality W V f := by
    change f.hom.hom.val.left ≫ structureMap i V.obj = structureMap i W.obj ≫ 𝟙 X
    rw [Category.comp_id]
    exact MorphismProperty.Over.w f.hom.hom.val

instance stageEtale (W : ExactAffinePointed i) : Etale ((stagesToBase i).app W) :=
  inferInstanceAs (Etale (structureMap i W.obj))

abbrev diagram : (ExactAffinePointed i)ᵒᵖ ⥤ CommRingCat.{u} := (schemes i).op ⋙ Scheme.Γ

section Colimit

variable [IsAffine X] [IsClosedImmersion i]

instance : HasColimitsOfShape (ExactAffinePointed i)ᵒᵖ CommRingCat.{u} :=
  hasColimitsOfShape_of_finallySmall _ _

/-- The ring of germs on affine étale neighborhoods of the closed subscheme. -/
abbrev germs : CommRingCat.{u} := colimit (diagram i)

abbrev germ (W : ExactAffinePointed i) : Γ((schemes i).obj W, ⊤) ⟶ germs i :=
  colimit.ι (diagram i) (op W)

private def evalCocone : Cocone (diagram i) where
  pt := Γ(Z, ⊤)
  ι := {
    app := fun W => (point i W.unop.obj).appTop
    naturality := fun U V a => by
      let k := a.unop.hom.hom
      change k.val.left.appTop ≫ (point i V.unop.obj).appTop =
        (point i U.unop.obj).appTop ≫ 𝟙 _
      rw [← Scheme.Hom.comp_appTop, Category.comp_id]
      exact congrArg Scheme.Hom.appTop (congrArg Over.Hom.left k.property) }

/-- Evaluate germs on the section at the closed subscheme. -/
def evaluate : germs i ⟶ Γ(Z, ⊤) := colimit.desc _ (evalCocone i)

@[reassoc]
theorem germ_evaluate (W : ExactAffinePointed i) :
    germ i W ≫ evaluate i = (point i W.obj).appTop :=
  colimit.ι_desc (evalCocone i) (op W)

theorem evaluation_surjective : Function.Surjective (evaluate i) := by
  let W : ExactAffinePointed i :=
    ⟨mkAffine i (𝟙 X) i (Category.comp_id i), IsPullback.of_id_snd⟩
  intro z
  obtain ⟨a, ha⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2 z
  exact ⟨germ i W a, (ConcreteCategory.congr_hom (germ_evaluate i W) a).trans ha⟩

private theorem exists_representative (x : germs i) :
    ∃ (W : ExactAffinePointed i) (b : Γ((schemes i).obj W, ⊤)), germ i W b = x := by
  let F := InitiallySmall.fromCofilteredInitialModel.{u} (ExactAffinePointed i)
  let c := colimit.cocone (diagram i)
  let hc := (Functor.Final.isColimitWhiskerEquiv F.op c).symm (colimit.isColimit _)
  obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget CommRingCat) hc) x
  exact ⟨F.obj j.unop, b, hb⟩

/-- A germ is a unit when its value on the closed subscheme is a unit.
Inverting a representative amounts to passing to a principal open neighborhood. -/
theorem isUnit_iff_evaluate (x : germs i) : IsUnit x ↔ IsUnit (evaluate i x) := by
  refine ⟨fun h => h.map (evaluate i).hom, ?_⟩
  obtain ⟨W, b, rfl⟩ := exists_representative i x
  intro h
  have hu : IsUnit ((point i W.obj).appTop b) :=
    (ConcreteCategory.congr_hom (germ_evaluate i W) b) ▸ h
  let V := (ambient i W.obj).basicOpen b
  have hV : IsAffineOpen V := by
    let : IsAffine (ambient i W.obj) := W.obj.property
    exact (isAffineOpen_top (ambient i W.obj)).basicOpen b
  have hr : Set.range (point i W.obj) ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change z ∈ point i W.obj ⁻¹ᵁ V
    rw [Scheme.preimage_basicOpen_top, Z.basicOpen_of_isUnit hu]
    exact trivial
  let t := IsOpenImmersion.lift V.ι (point i W.obj) hr
  have ht : t ≫ V.ι = point i W.obj := IsOpenImmersion.lift_fac ..
  let : IsAffine V.toScheme := hV
  obtain ⟨U, z, hU, hz, hb⟩ := exists_affine_refinement i (V.ι ≫ structureMap i W.obj) t
    (by rw [← Category.assoc, ht]; exact point_comp i W.obj)
  let : IsAffine U.toScheme := hU
  let W' : ExactAffinePointed i := ⟨mkAffine i (U.ι ≫ (V.ι ≫ structureMap i W.obj)) z
    (hb.w.trans (Category.id_comp i)), hb⟩
  let k : W' ⟶ W := ⟨homMk i (U.ι ≫ V.ι) (Category.assoc _ _ _) (by
    change z ≫ (U.ι ≫ V.ι) = point i W.obj
    rw [← Category.assoc, hz, ht])⟩
  have hv : IsUnit (V.ι.appTop b) := by
    apply RingedSpace.isUnit_of_isUnit_germ V.toScheme.toRingedSpace
    intro y hy
    apply (V.toScheme.mem_basicOpen_top _ _).mp
    rw [← Scheme.preimage_basicOpen_top]
    exact y.property
  have hk : IsUnit (((diagram i).map k.op) b) := by
    change IsUnit ((U.ι ≫ V.ι).appTop b)
    rw [Scheme.Hom.comp_appTop]
    exact hv.map U.ι.appTop.hom
  have e : (diagram i).map k.op ≫ germ i W' = germ i W := colimit.w (diagram i) k.op
  exact (ConcreteCategory.congr_hom e b) ▸ hk.map (germ i W').hom

/-- The ideal of functions vanishing on the closed subscheme lies in the
Jacobson radical of the neighborhood colimit. -/
theorem ker_evaluate_le_jacobson :
    RingHom.ker (evaluate i).hom ≤ Ideal.jacobson ⊥ := by
  intro x hx
  apply Ideal.mem_jacobson_iff.mpr
  intro y
  have h : IsUnit (y * x + 1) := (isUnit_iff_evaluate i _).mpr (by
    change IsUnit ((evaluate i).hom (y * x + 1))
    rw [map_add, map_mul, RingHom.mem_ker.mp hx, mul_zero, zero_add, map_one]
    exact isUnit_one)
  obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.mp h
  refine ⟨z, Ideal.mem_bot.mpr ?_⟩
  calc
    z * y * x + z - 1 = (y * x + 1) * z - 1 := by rw [add_mul, one_mul, mul_assoc, mul_comm z]
    _ = 0 := sub_eq_zero.mpr hz

private theorem exists_representatives {J : Type*} [Fintype J] (x : J → germs i) :
    ∃ (W : ExactAffinePointed i) (b : J → Γ((schemes i).obj W, ⊤)),
      ∀ j, germ i W (b j) = x j := by
  classical
  choose W b hb using fun j => exists_representative i (x j)
  obtain ⟨V, hV⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image W)
  let v (j : J) : V ⟶ W j := (hV (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)).some
  refine ⟨V, fun j => (diagram i).map (v j).op (b j), fun j => ?_⟩
  exact (ConcreteCategory.congr_hom (colimit.w (diagram i) (v j).op) (b j)).trans (hb j)

private def affineToSpec : schemes i ≅ schemes i ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := by
  let α := (schemes i).whiskerLeft ΓSpec.adjunction.unit
  have (W : ExactAffinePointed i) : IsIso (α.app W) := by
    let : IsAffine ((schemes i).obj W) := W.obj.property
    change IsIso ((schemes i).obj W).toSpecΓ
    exact IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The spectrum of the neighborhood colimit is the limit of the affine neighborhoods. -/
def limitCone : LimitCone (schemes i) := by
  let c := coneRightOpOfCocone (colimit.cocone (diagram i))
  let hc := isLimitConeRightOpOfCocone _ (colimit.isColimit (diagram i))
  exact ⟨(Cone.postcompose (affineToSpec i).inv).obj (Scheme.Spec.mapCone c),
    (IsLimit.postcomposeHomEquiv (affineToSpec i).symm _).symm (isLimitOfPreserves Scheme.Spec hc)⟩

private abbrev identityNeighborhood : ExactAffinePointed i :=
  ⟨mkAffine i (𝟙 X) i (Category.comp_id i), IsPullback.of_id_snd⟩

def toBase : Spec (germs i) ⟶ X := (limitCone i).cone.π.app (identityNeighborhood i)

def toLimit : Z ⟶ Spec (germs i) := Z.toSpecΓ ≫ Spec.map (evaluate i)

private theorem projection_comp (W : ExactAffinePointed i) :
    (limitCone i).cone.π.app W ≫ structureMap i W.obj = toBase i := by
  let f : W ⟶ identityNeighborhood i :=
    ⟨homMk i (structureMap i W.obj) (Category.comp_id _) (point_comp i W.obj)⟩
  exact (limitCone i).cone.w f

theorem projection_toBase (W : ExactAffinePointed i) :
    (limitCone i).cone.π.app W ≫ (stagesToBase i).app W = toBase i :=
  projection_comp i W

private theorem point_projection (W : ExactAffinePointed i) :
    toLimit i ≫ (limitCone i).cone.π.app W = point i W.obj := by
  change (Z.toSpecΓ ≫ Spec.map (evaluate i)) ≫ Spec.map (germ i W) ≫
    (affineToSpec i).inv.app W = point i W.obj
  rw [Category.assoc, ← Spec.map_comp_assoc, germ_evaluate, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc]
  change point i W.obj ≫ (affineToSpec i).hom.app W ≫ (affineToSpec i).inv.app W = point i W.obj
  rw [Iso.hom_inv_id_app]
  exact Category.comp_id (show Z ⟶ (schemes i).obj W from point i W.obj)

/-- The limit has the prescribed closed fiber, with the section given by evaluation. -/
theorem isPullback_toLimit : IsPullback (toLimit i) (𝟙 Z) (toBase i) i := by
  refine IsPullback.of_isLimit' ⟨(point_projection i (identityNeighborhood i)).trans
    (Category.id_comp i).symm⟩ (PullbackCone.IsLimit.mk _ (fun c => c.snd) ?_
      (fun c => Category.comp_id c.snd) (fun c m _ hm => (Category.comp_id m).symm.trans hm))
  intro c
  apply (limitCone i).isLimit.hom_ext
  intro W
  rw [Category.assoc, point_projection]
  obtain ⟨z, h₁, h₂⟩ := W.property.exists_lift (c.fst ≫ (limitCone i).cone.π.app W) c.snd
    (by rw [Category.assoc, projection_comp]; exact c.condition)
  have he : z = c.snd := (Category.comp_id z).symm.trans h₂
  exact he ▸ h₁

private theorem exists_root_of_stage (W : ExactAffinePointed i)
    (p : (Γ((schemes i).obj W, ⊤))[X]) (hp : p.Monic) (a : Γ(Z, ⊤))
    (ha : p.eval₂ (point i W.obj).appTop.hom a = 0)
    (hder : IsUnit (p.derivative.eval₂ (point i W.obj).appTop.hom a)) :
    ∃ b : germs i, p.eval₂ (germ i W).hom b = 0 ∧ evaluate i b = a := by
  let Y := (schemes i).obj W
  let : IsAffine Y := W.obj.property
  let B := Γ(Y, ⊤)
  let t : Z ⟶ Y := point i W.obj
  let g : Y ⟶ X := structureMap i W.obj
  let P : StandardEtalePair B := ⟨p, hp, p.derivative, 1, 0, 1,
    by rw [mul_one, mul_zero, add_zero, pow_one]⟩
  let C := CommRingCat.of P.Ring
  let e : B ⟶ C := CommRingCat.ofHom (algebraMap B P.Ring)
  let : Algebra B Γ(Z, ⊤) := t.appTop.hom.toAlgebra
  have hP : P.HasMap a := ⟨ha, hder⟩
  let r : C ⟶ Γ(Z, ⊤) := CommRingCat.ofHom (P.lift a hP).toRingHom
  have her : e ≫ r = t.appTop := by
    apply ConcreteCategory.hom_ext
    exact (P.lift a hP).commutes
  let q := Spec.map e ≫ Y.isoSpec.inv
  let : Etale (Spec.map e) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let z₀ := Z.toSpecΓ ≫ Spec.map r
  have hz₀ : z₀ ≫ q = t := by
    change (Z.toSpecΓ ≫ Spec.map r) ≫ Spec.map e ≫ Y.isoSpec.inv = t
    calc
      _ = (Z.toSpecΓ ≫ Spec.map (e ≫ r)) ≫ Y.isoSpec.inv := by
        simp only [Spec.map_comp, Category.assoc]
      _ = t := by
        rw [her, ← Scheme.toSpecΓ_naturality, Category.assoc]
        change t ≫ Y.isoSpec.hom ≫ Y.isoSpec.inv = t
        rw [Iso.hom_inv_id, Category.comp_id]
  obtain ⟨V, z, hV, hz, hpb⟩ := exists_affine_refinement i (q ≫ g) z₀
    (by rw [← Category.assoc, hz₀]; exact point_comp i W.obj)
  let : IsAffine V.toScheme := hV
  let U : ExactAffinePointed i :=
    ⟨mkAffine i (V.ι ≫ (q ≫ g)) z (hpb.w.trans (Category.id_comp i)), hpb⟩
  let k : U ⟶ W := ⟨homMk i (V.ι ≫ q) (Category.assoc _ _ _) (by
    change z ≫ (V.ι ≫ q) = t
    rw [← Category.assoc, hz, hz₀])⟩
  let β : C ⟶ germs i := (Scheme.ΓSpecIso C).inv ≫ V.ι.appTop ≫ germ i U
  have hY : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso B).inv := by
    have H := congrArg Scheme.Hom.appTop Y.isoSpec.hom_inv_id
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at H
    change Y.isoSpec.inv.appTop ≫ Y.toSpecΓ.appTop = 𝟙 B at H
    rw [Scheme.toSpecΓ_appTop] at H
    exact (Iso.eq_comp_inv _).mpr (H.trans (Category.id_comp _).symm)
  have hq : q.appTop = e ≫ (Scheme.ΓSpecIso C).inv := by
    change (Spec.map e ≫ Y.isoSpec.inv).appTop = _
    rw [Scheme.Hom.comp_appTop, hY, Scheme.ΓSpecIso_inv_naturality]
  have hβ : e ≫ β = germ i W := by
    change e ≫ (Scheme.ΓSpecIso C).inv ≫ V.ι.appTop ≫ germ i U = germ i W
    rw [← Category.assoc, ← hq, ← Category.assoc, ← Scheme.Hom.comp_appTop]
    exact colimit.w (diagram i) k.op
  have hβr : β ≫ evaluate i = r := by
    change ((Scheme.ΓSpecIso C).inv ≫ V.ι.appTop ≫ germ i U) ≫ evaluate i = r
    rw [Category.assoc, Category.assoc, germ_evaluate]
    change (Scheme.ΓSpecIso C).inv ≫ V.ι.appTop ≫ z.appTop = r
    rw [← Scheme.Hom.comp_appTop, hz]
    change (Scheme.ΓSpecIso C).inv ≫ (Z.toSpecΓ ≫ Spec.map r).appTop = r
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  refine ⟨β P.X, ?_, ?_⟩
  · have hroot : p.eval₂ e.hom P.X = 0 := (StandardEtalePair.hasMap_X (P := P)).1
    rw [← hβ, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, hroot, map_zero]
  · exact (ConcreteCategory.congr_hom hβr P.X).trans (P.lift_X a hP)

/-- A simple root on the closed subscheme lifts to the neighborhood colimit. -/
theorem exists_lift_root {p : (germs i)[X]} (hp : p.Monic) (a : Γ(Z, ⊤))
    (ha : p.eval₂ (evaluate i).hom a = 0) (hder : IsUnit (p.derivative.eval₂ (evaluate i).hom a)) :
    ∃ b : germs i, p.IsRoot b ∧ evaluate i b = a := by
  obtain ⟨W, b, hb⟩ := exists_representatives i (fun j : p.support => p.coeff j)
  have hlifts : p ∈ Polynomial.lifts (germ i W).hom := by
    apply (Polynomial.lifts_iff_coeff_lifts p).mpr
    intro j
    by_cases hj : j ∈ p.support
    · exact ⟨b ⟨j, hj⟩, hb ⟨j, hj⟩⟩
    · exact ⟨0, by rw [map_zero, Polynomial.notMem_support_iff.mp hj]⟩
  obtain ⟨q, rfl, _, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hEval : (evaluate i).hom.comp (germ i W).hom = (point i W.obj).appTop.hom :=
    congrArg CommRingCat.Hom.hom (germ_evaluate i W)
  rw [Polynomial.eval₂_map, hEval] at ha
  rw [Polynomial.derivative_map, Polynomial.eval₂_map, hEval] at hder
  obtain ⟨c, hc, hca⟩ := exists_root_of_stage i W q hq a ha hder
  exact ⟨c, (Polynomial.eval_map _ _).trans hc, hca⟩

/-- The evaluation kernel defines a henselian pair on the colimit. -/
theorem henselian : HenselianRing (germs i) (RingHom.ker (evaluate i).hom) where
  jac := ker_evaluate_le_jacobson i
  is_henselian p hp a ha hder := by
    have hroot : p.eval₂ (evaluate i).hom (evaluate i a) = 0 :=
      (Polynomial.eval₂_at_apply _ _).trans (RingHom.mem_ker.mp ha)
    let ρ := Ideal.Quotient.lift (RingHom.ker (evaluate i).hom) (evaluate i).hom
      (fun _ hx => RingHom.mem_ker.mp hx)
    have hu : IsUnit ((evaluate i).hom (p.derivative.eval a)) := hder.map ρ
    rw [← Polynomial.eval₂_at_apply] at hu
    obtain ⟨b, hb, hba⟩ := exists_lift_root i hp (evaluate i a) hroot hu
    refine ⟨b, hb, RingHom.mem_ker.mpr ?_⟩
    rw [map_sub, sub_eq_zero]
    exact hba

end Colimit

end PhilipponHenselianPairNeighborhoods

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)


namespace PhilipponEtaleSkyscraperAcyclicity

universe u

private abbrev Ab := AddCommGrpCat.{u}

private theorem epi_pi_map {I : Type u} {M N : I → Ab.{u}} (a : ∀ i, M i ⟶ N i)
    (ha : ∀ i, Epi (a i)) : Epi (Limits.Pi.map a) := by
  let b : Discrete.functor M ⟶ Discrete.functor N := Discrete.natTrans (fun i => a i.as)
  have : Epi b := (NatTrans.epi_iff_epi_app _).mpr (fun i => ha i.as)
  change Epi ((lim (J := Discrete I) (C := Ab.{u})).map b)
  exact preserves_epi_of_preservesColimit lim b

variable {X : Scheme.{u}} (Φ : X.smallEtaleTopology.Point.{u})

private abbrev skyscraper := Φ.skyscraperSheafFunctor (A := Ab.{u})

/-- A map of skyscraper sheaves induced by a surjection of coefficients
is surjective on every étale chart. -/
theorem skyscraper_app_epi {M N : Ab.{u}} (a : M ⟶ N) [Epi a] (W : X.Etaleᵒᵖ) :
    Epi (((skyscraper Φ).map a).hom.app W) :=
  epi_pi_map (fun _ : Φ.fiber.obj W.unop => a) (fun _ => inferInstance)

/-- A family of surjections on coefficients induces a surjection on each
chart after taking the product of the associated skyscraper sheaves. -/
theorem product_skyscraper_app_epi {I : Type u} (points : I → X.smallEtaleTopology.Point.{u})
    {M N : I → Ab.{u}} (a : ∀ i, M i ⟶ N i) (ha : ∀ i, Epi (a i)) (W : X.Etaleᵒᵖ) :
    Epi ((Limits.Pi.map (fun i => (skyscraper (points i)).map (a i))).hom.app W) := by
  let F := sheafToPresheaf X.smallEtaleTopology Ab.{u} ⋙ (evaluation _ _).obj W
  have : PreservesLimitsOfShape (Discrete I) F := comp_preservesLimitsOfShape _ _
  let S (i : I) := (skyscraper (points i)).obj (M i)
  let T (i : I) := (skyscraper (points i)).obj (N i)
  let f (i : I) : S i ⟶ T i := (skyscraper (points i)).map (a i)
  let eS := PreservesProduct.iso F S
  let eT := PreservesProduct.iso F T
  have h : F.map (Limits.Pi.map f) ≫ eT.hom = eS.hom ≫ Limits.Pi.map (fun i => F.map (f i)) := by
    apply Pi.hom_ext
    intro i
    simp only [eS, eT, Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
      piComparison_comp_π_assoc, Pi.map_π, ← F.map_comp]
  have : Epi (Limits.Pi.map (fun i => F.map (f i))) := epi_pi_map _ (fun i => by
    let : Epi (a i) := ha i
    exact skyscraper_app_epi (points i) (a i) W)
  change Epi (F.map (Limits.Pi.map f))
  apply (epi_comp_iff_of_isIso _ eT.hom).mp
  rw [h]
  infer_instance

/-- Skyscraper sheaves at a point of the étale site are exact in their
abelian coefficient group. -/
theorem preservesFiniteColimits : PreservesFiniteColimits (skyscraper Φ) := by
  let R := skyscraper Φ
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  have : R.PreservesEpimorphisms := by
    constructor
    intro M N a _
    have : Epi ((R.map a).hom) :=
      (NatTrans.epi_iff_epi_app _).mpr (skyscraper_app_epi Φ a)
    exact Sheaf.Hom.epi_of_presheaf_epi (J := X.smallEtaleTopology) (A := Ab.{u}) (R.map a)
  have : R.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels R
  exact Functor.preservesFiniteColimits_of_preservesHomology R

variable {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)

/-- The global sections of a skyscraper sheaf are its coefficient group. -/
def skyscraperGlobalSectionsIso :
    skyscraper (Scheme.pointSmallEtale s) ⋙ globalSections X ≅ 𝟭 Ab.{u} := by
  let T := Scheme.Etale.mk (𝟙 X)
  let I := (Scheme.pointSmallEtale s).fiber.obj T
  let t : I := Over.homMk s (Category.comp_id _)
  have ht (x : I) : x = t := by
    apply Over.OverMorphism.ext
    exact (Category.comp_id x.left).symm.trans (Over.w x)
  refine NatIso.ofComponents (fun M => ?_) (fun a => ?_)
  · refine ⟨Pi.π (fun _ : I => M) t, Pi.lift (fun _ : I => 𝟙 M), ?_, ?_⟩
    · apply Pi.hom_ext
      intro x
      rw [Category.assoc, Pi.lift_π]
      change Pi.π (fun _ : I => M) t ≫ 𝟙 M =
        𝟙 (∏ᶜ fun _ : I => M) ≫ Pi.π (fun _ : I => M) x
      rw [Category.comp_id, Category.id_comp, ht x]
    · exact Pi.lift_π (fun _ : I => 𝟙 M) t
  · exact Pi.map_π (fun _ : I => a) t

/-- A skyscraper sheaf at a geometric point has trivial positive étale
cohomology, with any abelian coefficient group. -/
theorem skyscraper_H_succ (M : Ab.{u}) (q : ℕ) :
    Subsingleton (((skyscraper (Scheme.pointSmallEtale s)).obj M).H (q + 1)) := by
  let Φ := Scheme.pointSmallEtale s
  let R := skyscraper Φ
  let Γ := globalSections X
  let : Γ.Additive := ⟨fun {_ _} _ _ => rfl⟩
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : PreservesFiniteColimits R := preservesFiniteColimits Φ
  let : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      Φ.skyscraperSheafAdjunction
  let I := injectiveResolution M
  have hR (k : ℕ) : IsZero ((R.rightDerived (k + 1)).obj M) := by
    let L := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    have hL : L.ExactAt (k + 1) :=
      (show (I.cocomplex.sc (k + 1)).Exact from I.cocomplex_exactAt_succ k).map R
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hL).of_iso
      (I.isoRightDerivedObj R (k + 1))
  let J := PhilipponDerivedAdjunction.mapInjectiveResolution R I hR
  let H := HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℕ) (q + 1)
  let e := (NatIso.mapHomologicalComplex (skyscraperGlobalSectionsIso s) (ComplexShape.up ℕ) ≪≫
    Functor.mapHomologicalComplexIdIso Ab.{u} (ComplexShape.up ℕ)).app I.cocomplex
  have h0 : IsZero (H.obj I.cocomplex) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (I.cocomplex_exactAt_succ q)
  have h1 : IsZero (H.obj ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)) :=
    h0.of_iso (H.mapIso e)
  let c := PhilipponEtaleDerivedSections.cohomologyEquivResolution (R.obj M) J (q + 1)
  exact ⟨fun a b => c.injective ((AddCommGrpCat.subsingleton_of_isZero h1).elim (c a) (c b))⟩

end PhilipponEtaleSkyscraperAcyclicity

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (geometricMap geometricPoint)
open PhilipponEtaleSkyscraperAcyclicity (product_skyscraper_app_epi skyscraperGlobalSectionsIso)


namespace PhilipponEtaleSkyscraperProducts

universe u

private abbrev Ab := AddCommGrpCat.{u}
private abbrev Sh (X : Scheme.{u}) := Sheaf X.smallEtaleTopology Ab.{u}

variable {X : Scheme.{u}} {I : Type u} (points : I → X)

private abbrev Φ (i : I) := geometricPoint (points i)

private abbrev coefficients (I : Type u) := Discrete I ⥤ Ab.{u}

private abbrev adj (i : I) := (Φ points i).skyscraperSheafAdjunction (A := Ab.{u})

/-- The family of geometric stalks of a sheaf. -/
def stalks : Sh X ⥤ coefficients I where
  obj F := Discrete.functor (fun i => ((Φ points i).sheafFiber (A := Ab.{u})).obj F)
  map a := Discrete.natTrans (fun i => ((Φ points i.as).sheafFiber (A := Ab.{u})).map a)
  map_id F := by
    apply NatTrans.ext
    funext i
    exact ((Φ points i.as).sheafFiber (A := Ab.{u})).map_id F
  map_comp a b := by
    apply NatTrans.ext
    funext i
    exact ((Φ points i.as).sheafFiber (A := Ab.{u})).map_comp a b

private abbrev skyscrapers (M : coefficients I) (i : I) :=
  (Φ points i).skyscraperSheaf (M.obj ⟨i⟩)

/-- The product of the geometric skyscraper sheaves of a family of abelian groups. -/
def product : coefficients I ⥤ Sh X where
  obj M := ∏ᶜ skyscrapers points M
  map a := Limits.Pi.map (fun i => (Φ points i).skyscraperSheafFunctor.map (a.app ⟨i⟩))
  map_id M := by
    let S := skyscrapers points M
    have h : (fun i : I => (Φ points i).skyscraperSheafFunctor.map (𝟙 (M.obj ⟨i⟩))) =
        fun i => 𝟙 (S i) := funext fun i => (Φ points i).skyscraperSheafFunctor.map_id _
    exact (congrArg Limits.Pi.map h).trans Limits.Pi.map_id
  map_comp a b := by
    simp only [NatTrans.comp_app, Functor.map_comp]
    exact (Limits.Pi.map_comp_map _ _).symm

/-- The product of skyscraper sheaves is right adjoint to the family of stalks. -/
def productAdjunction : stalks points ⊣ product points :=
  Adjunction.mkOfHomEquiv
    { homEquiv F M :=
        { toFun := fun a => Pi.lift (fun i => (adj points i).homEquiv F (M.obj ⟨i⟩) (a.app ⟨i⟩))
          invFun := fun b => Discrete.natTrans (fun i =>
            ((adj points i.as).homEquiv F (M.obj i)).symm (b ≫ Pi.π _ i.as))
          left_inv := by
            intro a
            apply NatTrans.ext
            funext i
            change ((adj points i.as).homEquiv F (M.obj i)).symm
              (Pi.lift (fun j => (adj points j).homEquiv F (M.obj ⟨j⟩) (a.app ⟨j⟩)) ≫
                Pi.π _ i.as) = a.app i
            rw [Pi.lift_π]
            cases i
            exact Equiv.symm_apply_apply _ _
          right_inv := by
            intro b
            apply Pi.hom_ext
            intro i
            exact (Pi.lift_π _ _).trans (Equiv.apply_symm_apply _ _) }
      homEquiv_naturality_left_symm a b := by
        apply NatTrans.ext
        funext i
        exact (congrArg (((adj points i.as).homEquiv _ _).symm) (Category.assoc _ _ _)).trans
          ((adj points i.as).homEquiv_naturality_left_symm _ _)
      homEquiv_naturality_right {K M N} a b := by
        apply Pi.hom_ext
        intro i
        change Pi.lift (fun j => (adj points j).homEquiv K (N.obj ⟨j⟩) ((a ≫ b).app ⟨j⟩)) ≫
            Pi.π (skyscrapers points N) i =
          (Pi.lift (fun j => (adj points j).homEquiv K (M.obj ⟨j⟩) (a.app ⟨j⟩)) ≫
            Limits.Pi.map (fun j => (Φ points j).skyscraperSheafFunctor.map (b.app ⟨j⟩))) ≫
            Pi.π (skyscrapers points N) i
        simp only [Category.assoc, Pi.lift_π, Pi.map_π, Pi.lift_π_assoc, NatTrans.comp_app]
        exact (adj points i).homEquiv_naturality_right _ _ }

/-- Taking a product of geometric skyscraper sheaves is exact in the
family of abelian coefficient groups. -/
theorem product_preservesFiniteColimits : PreservesFiniteColimits (product points) := by
  let R := product points
  have : R.IsRightAdjoint := (productAdjunction points).isRightAdjoint
  have : R.Additive := Functor.additive_of_preserves_binary_products R
  have : R.PreservesEpimorphisms := by
    constructor
    intro M N a ha
    have h (i : I) : Epi (a.app ⟨i⟩) := (NatTrans.epi_iff_epi_app _).mp ha ⟨i⟩
    have : Epi ((R.map a).hom) :=
      (NatTrans.epi_iff_epi_app _).mpr
        (product_skyscraper_app_epi (Φ points) (fun i => a.app ⟨i⟩) h)
    exact Sheaf.Hom.epi_of_presheaf_epi (J := X.smallEtaleTopology) (A := Ab.{u}) (R.map a)
  have : R.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels R
  exact Functor.preservesFiniteColimits_of_preservesHomology R

private def sectionsIso : product points ⋙ globalSections X ≅ lim (J := Discrete I) (C := Ab.{u}) := by
  let Γ := globalSections X
  let U := Scheme.Etale.mk (𝟙 X)
  have : PreservesLimitsOfShape (Discrete I) Γ :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete I)
      (sheafToPresheaf X.smallEtaleTopology Ab.{u} ⋙ (evaluation _ _).obj (op U)))
  let σ (M : coefficients I) (i : I) : Γ.obj (skyscrapers points M i) ≅ M.obj ⟨i⟩ :=
    (skyscraperGlobalSectionsIso (geometricMap (points i))).app (M.obj ⟨i⟩)
  let e (M : coefficients I) : Γ.obj (∏ᶜ skyscrapers points M) ≅ limit M :=
    PreservesProduct.iso Γ (skyscrapers points M) ≪≫ Limits.Pi.mapIso (σ M) ≪≫ Pi.isoLimit M
  have he (M : coefficients I) (i : I) :
      (e M).hom ≫ limit.π M ⟨i⟩ = Γ.map (Pi.π (skyscrapers points M) i) ≫ (σ M i).hom := by
    simp only [e, Iso.trans_hom, Category.assoc, Pi.isoLimit_hom_π, Pi.mapIso_hom_π,
      PreservesProduct.iso_hom, piComparison_comp_π_assoc]
  refine NatIso.ofComponents e (fun {M N} a => ?_)
  apply limit.hom_ext
  rintro ⟨i⟩
  change (Γ.map (Limits.Pi.map (fun j => (Φ points j).skyscraperSheafFunctor.map (a.app ⟨j⟩))) ≫
      (e N).hom) ≫ limit.π N ⟨i⟩ = ((e M).hom ≫ limMap a) ≫ limit.π N ⟨i⟩
  rw [Category.assoc, he, ← Γ.map_comp_assoc, Pi.map_π, Γ.map_comp, Category.assoc,
    Category.assoc, limMap_π]
  have hσ : Γ.map ((Φ points i).skyscraperSheafFunctor.map (a.app ⟨i⟩)) ≫ (σ N i).hom =
      (σ M i).hom ≫ a.app ⟨i⟩ :=
    (skyscraperGlobalSectionsIso (geometricMap (points i))).hom.naturality (a.app ⟨i⟩)
  calc
    _ = Γ.map (Pi.π (skyscrapers points M) i) ≫ ((σ M i).hom ≫ a.app ⟨i⟩) := by
      simpa only [Category.assoc] using congrArg (Γ.map (Pi.π (skyscrapers points M) i) ≫ ·) hσ
    _ = _ := by
      simpa only [Category.assoc] using congrArg (· ≫ a.app ⟨i⟩) (he M i).symm

private instance : EnoughInjectives (coefficients I) where
  presentation M := by
    let J := Discrete.functor (fun i : I => Injective.under (M.obj ⟨i⟩))
    have (i : Discrete I) : Injective (J.obj i) :=
      inferInstanceAs (Injective (Injective.under (M.obj ⟨i.as⟩)))
    let b : M ⟶ J := Discrete.natTrans (fun i => Injective.ι (M.obj i))
    have hJ : Injective J := by
      constructor
      intro A B g f hf
      have (i : Discrete I) : Mono (f.app i) := (NatTrans.mono_iff_mono_app _).mp hf i
      let r : B ⟶ J := Discrete.natTrans (fun i => Injective.factorThru (g.app i) (f.app i))
      refine ⟨r, ?_⟩
      apply NatTrans.ext
      funext i
      exact Injective.comp_factorThru (g.app i) (f.app i)
    exact ⟨⟨J, hJ, b, (NatTrans.mono_iff_mono_app _).mpr (fun i => Injective.ι_mono (M.obj i))⟩⟩

/-- Arbitrary small products of geometric skyscraper sheaves have zero
positive étale cohomology. -/
theorem product_H_succ (M : coefficients I) (q : ℕ) :
    Subsingleton (((product points).obj M).H (q + 1)) := by
  let R := product points
  let Γ := globalSections X
  let G := lim (J := Discrete I) (C := Ab.{u})
  let : R.IsRightAdjoint := (productAdjunction points).isRightAdjoint
  let : Γ.Additive := ⟨fun {_ _} _ _ => rfl⟩
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : G.Additive := Functor.additive_of_preserves_binary_products G
  let : PreservesFiniteColimits R := product_preservesFiniteColimits points
  let : (stalks points).PreservesMonomorphisms := by
    constructor
    intro A B f _
    exact (NatTrans.mono_iff_mono_app _).mpr (fun i =>
      inferInstanceAs (Mono (((Φ points i.as).sheafFiber (A := Ab.{u})).map f)))
  let : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (productAdjunction points)
  let J := injectiveResolution M
  have hf (k : ℕ) : IsZero ((R.rightDerived (k + 1)).obj M) := by
    let K := (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    have hK : K.ExactAt (k + 1) :=
      (show (J.cocomplex.sc (k + 1)).Exact from J.cocomplex_exactAt_succ k).map R
    exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hK).of_iso
      (J.isoRightDerivedObj R (k + 1))
  let J' := PhilipponDerivedAdjunction.mapInjectiveResolution R J hf
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  have hK : K.ExactAt (q + 1) :=
    (show (J.cocomplex.sc (q + 1)).Exact from J.cocomplex_exactAt_succ q).map G
  let H := HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℕ) (q + 1)
  let e := (NatIso.mapHomologicalComplex (sectionsIso points) (ComplexShape.up ℕ)).app J.cocomplex
  have hZ : IsZero (H.obj ((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj J'.cocomplex)) :=
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hK).of_iso (H.mapIso e)
  let c := PhilipponEtaleDerivedSections.cohomologyEquivResolution (R.obj M) J' (q + 1)
  exact ⟨fun a b => c.injective ((AddCommGrpCat.subsingleton_of_isZero hZ).elim (c a) (c b))⟩

/-- Products of geometric skyscraper sheaves are acyclic for étale direct
image along any scheme morphism. -/
theorem isZero_higherDirectImage_product {Y : Scheme.{u}} (f : X ⟶ Y)
    (M : coefficients I) (q : ℕ) :
    IsZero (((pushforward f).rightDerived (q + 1)).obj ((product points).obj M)) := by
  let R := product points
  let D := pushforward f
  let : R.IsRightAdjoint := (productAdjunction points).isRightAdjoint
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : PreservesFiniteColimits R := product_preservesFiniteColimits points
  let : (stalks points).PreservesMonomorphisms := by
    constructor
    intro A B a _
    exact (NatTrans.mono_iff_mono_app _).mpr (fun i =>
      inferInstanceAs (Mono (((Φ points i.as).sheafFiber (A := Ab.{u})).map a)))
  let : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (productAdjunction points)
  let P := R ⋙ D
  let : P.PreservesEpimorphisms := by
    constructor
    intro A B a ha
    have : Epi (P.map a).hom := by
      apply (NatTrans.epi_iff_epi_app _).mpr
      intro W
      change Epi ((R.map a).hom.app (op ((baseChange f).obj W.unop)))
      exact product_skyscraper_app_epi (Φ points) (fun i => a.app ⟨i⟩)
        (fun i => (NatTrans.epi_iff_epi_app _).mp ha ⟨i⟩) _
    exact Sheaf.Hom.epi_of_presheaf_epi (J := Y.smallEtaleTopology) (A := Ab.{u}) (P.map a)
  let : P.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels P
  let : PreservesFiniteColimits P := Functor.preservesFiniteColimits_of_preservesHomology P
  let J := injectiveResolution M
  have hR (k : ℕ) : IsZero ((R.rightDerived (k + 1)).obj M) := by
    apply IsZero.of_iso _ (J.isoRightDerivedObj R (k + 1))
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    exact (show (J.cocomplex.sc (k + 1)).Exact from J.cocomplex_exactAt_succ k).map R
  let J' := PhilipponDerivedAdjunction.mapInjectiveResolution R J hR
  let c := ComplexShape.up ℕ
  let H := HomologicalComplex.homologyFunctor (Sh Y) c (q + 1)
  let e := (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ D)) c).app J.cocomplex
  refine IsZero.of_iso ?_ (J'.isoRightDerivedObj D (q + 1) ≪≫ H.mapIso e)
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
  exact (show (J.cocomplex.sc (q + 1)).Exact from J.cocomplex_exactAt_succ q).map P

end PhilipponEtaleSkyscraperProducts

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (geometricPoint)


namespace PhilipponEtaleModuleSkyscrapers

universe u

variable {X : Scheme.{u}} {R : Type u} [Ring R]

private abbrev Modules := Sheaf X.smallEtaleTopology (ModuleCat.{u} R)

private abbrev stalk (x : X) := (geometricPoint x).sheafFiber (A := ModuleCat.{u} R)

private abbrev stalkAdjunction (x : X) :=
  (geometricPoint x).skyscraperSheafAdjunction (A := ModuleCat.{u} R)

private abbrev stalkSheaf (F : Modules (X := X) (R := R)) (x : X) :=
  (geometricPoint x).skyscraperSheaf ((stalk (R := R) x).obj F)

/-- The product of skyscraper sheaves of all the geometric stalks of a sheaf
of modules. -/
def pointProduct (F : Modules (X := X) (R := R)) : Modules (X := X) (R := R) :=
  ∏ᶜ stalkSheaf F

/-- The unit maps of the stalk-skyscraper adjunctions give a canonical
map into the product of geometric skyscrapers. -/
def toPointProduct (F : Modules (X := X) (R := R)) : F ⟶ pointProduct F :=
  Pi.lift fun x => (stalkAdjunction (R := R) x).unit.app F

private theorem mono_map_toPointProduct (F : Modules (X := X) (R := R)) (x : X) :
    Mono ((stalk (R := R) x).map (toPointProduct F)) := by
  let L := stalk (R := R) x
  let adj := stalkAdjunction (R := R) x
  have h : L.map (toPointProduct F) ≫
      (L.map (Pi.π (stalkSheaf F) x) ≫ adj.counit.app (L.obj F)) = 𝟙 (L.obj F) := by
    rw [← Category.assoc, ← L.map_comp, toPointProduct, Pi.lift_π]
    exact adj.left_triangle_components F
  exact mono_of_mono_fac h

/-- The geometric skyscraper product contains the original module sheaf as
a subobject. -/
theorem mono_toPointProduct (F : Modules (X := X) (R := R)) : Mono (toPointProduct F) := by
  let P : ObjectProperty (X.smallEtaleTopology.Point.{u}) :=
    ObjectProperty.ofObj (fun x : X => geometricPoint x)
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let : ∀ Φ : P.FullSubcategory,
      Mono ((Φ.obj.sheafFiber (A := ModuleCat.{u} R)).map (toPointProduct F)) := by
    intro Φ
    have h := Φ.property
    change ObjectProperty.ofObj (fun x : X => geometricPoint x) Φ.obj at h
    obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp h
    rw [← hx]
    exact mono_map_toPointProduct F x
  exact (hP.jointlyReflectMonomorphisms (ModuleCat.{u} R)).mono (toPointProduct F)

/-- An injective étale sheaf of modules is a retract of its geometric
skyscraper product. -/
theorem exists_retraction (F : Modules (X := X) (R := R)) [Injective F] :
    ∃ r : pointProduct F ⟶ F, toPointProduct F ≫ r = 𝟙 F := by
  let : Mono (toPointProduct F) := mono_toPointProduct F
  exact ⟨Injective.factorThru (𝟙 F) (toPointProduct F), Injective.comp_factorThru _ _⟩

private abbrev forgetModule := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

private instance : X.smallEtaleTopology.HasSheafCompose (forgetModule (R := R)) where
  isSheaf P hP := by
    apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u})
    exact Presheaf.isSheaf_comp_of_isSheaf _ P (CategoryTheory.forget (ModuleCat.{u} R)) hP

/-- Forget the module structure of an étale sheaf. -/
abbrev underlying : Modules (X := X) (R := R) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  sheafCompose X.smallEtaleTopology (forgetModule (R := R))

/-- Forgetting module structure preserves epimorphisms of étale sheaves. -/
theorem underlying_map_epi {F G : Modules (X := X) (R := R)}
    (a : F ⟶ G) [Epi a] : Epi (underlying.map a) := by
  let P : ObjectProperty (X.smallEtaleTopology.Point.{u}) :=
    ObjectProperty.ofObj (fun x : X => geometricPoint x)
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let : ∀ Φ : P.FullSubcategory,
      Epi ((Φ.obj.sheafFiber (A := AddCommGrpCat.{u})).map (underlying.map a)) := by
    intro Φ
    let L := Φ.obj.sheafFiber (A := ModuleCat.{u} R)
    let U := forgetModule (R := R)
    let e := Φ.obj.sheafFiberCompIso U
    have : Epi (L.map a) := Functor.map_epi L a
    have : Epi (U.map (L.map a)) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    change Epi (((underlying ⋙ Φ.obj.sheafFiber (A := AddCommGrpCat.{u}))).map a)
    apply (epi_comp_iff_of_isIso _ (e.hom.app G)).mp
    rw [e.hom.naturality a]
    exact epi_comp (e.hom.app F) (U.map (L.map a))
  exact (hP.jointlyReflectEpimorphisms AddCommGrpCat.{u}).epi (underlying.map a)

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

/-- Forgetting module structure preserves finite colimits. This can be
checked at the geometric stalks, where it is the forgetful functor on modules. -/
theorem underlying_preservesFiniteColimits :
    PreservesFiniteColimits (underlying (X := X) (R := R)) := by
  let U := forgetModule (R := R)
  let F := underlying (X := X) (R := R)
  let P : ObjectProperty (X.smallEtaleTopology.Point.{u}) :=
    ObjectProperty.ofObj (fun x : X => geometricPoint x)
  have hP : P.IsConservativeFamilyOfPoints := Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X
  let C (Φ : P.FullSubcategory) := Φ.obj.sheafFiber (A := AddCommGrpCat.{u})
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  have (Φ : P.FullSubcategory) : PreservesColimit (K ⋙ F) (C Φ) := by
    dsimp [C]
    infer_instance
  refine ⟨(hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).jointlyReflectsColimit
    (c := F.mapCocone c) ?_⟩
  intro Φ
  let e := Φ.obj.sheafFiberCompIso U
  have : PreservesColimitsOfShape J (F ⋙ C Φ) :=
    preservesColimitsOfShape_of_natIso e.symm
  change IsColimit ((F ⋙ C Φ).mapCocone c)
  exact isColimitOfPreserves (F ⋙ C Φ) hc

/-- The underlying abelian sheaf of a module skyscraper is the skyscraper
of its underlying abelian group. -/
def underlyingSkyscraperIso (Φ : X.smallEtaleTopology.Point.{u}) (M : ModuleCat.{u} R) :
    underlying.obj (Φ.skyscraperSheaf M) ≅ Φ.skyscraperSheaf ((forgetModule (R := R)).obj M) := by
  let U := forgetModule (R := R)
  let Q (W : X.Etaleᵒᵖ) (_ : Φ.fiber.obj W.unop) := M
  let T (W : X.Etaleᵒᵖ) (v : Φ.fiber.obj W.unop) := U.obj (Q W v)
  apply (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u}).preimageIso
  refine NatIso.ofComponents (fun W => PreservesProduct.iso U (Q W)) ?_
  intro W V a
  apply Pi.hom_ext
  intro x
  let k := Φ.fiber.map a.unop
  change (U.map (Limits.Pi.map' (f := Q W) (g := Q V) k (fun v => 𝟙 (Q V v))) ≫
      piComparison U (Q V)) ≫ Pi.π (T V) x =
    (piComparison U (Q W) ≫ Limits.Pi.map' (f := T W) (g := T V) k (fun v => 𝟙 (T V v))) ≫
      Pi.π (T V) x
  rw [Category.assoc, Category.assoc, piComparison_comp_π, ← U.map_comp,
    Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π, Category.comp_id]
  exact (piComparison_comp_π U (Q W) (k x)).symm

/-- Forgetting the coefficient module commutes with the product of
geometric skyscraper sheaves. -/
def underlyingPointProductIso (F : Modules (X := X) (R := R)) :
    underlying.obj (pointProduct F) ≅
      ∏ᶜ fun x : X => (geometricPoint x).skyscraperSheaf
        ((forgetModule (R := R)).obj ((stalk (R := R) x).obj F)) := by
  let U := forgetModule (R := R)
  let Mod := ModuleCat.{u} R
  let Ab := AddCommGrpCat.{u}
  let S := sheafToPresheaf X.smallEtaleTopology Ab
  let T := sheafToPresheaf X.smallEtaleTopology Mod
  let G := underlying (X := X) (R := R)
  have : PreservesLimitsOfShape (Discrete X) (G ⋙ S) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete X)
      (T ⋙ (Functor.whiskeringRight X.Etaleᵒᵖ Mod Ab).obj U))
  have : PreservesLimitsOfShape (Discrete X) G :=
    preservesLimitsOfShape_of_reflects_of_preserves G S
  exact PreservesProduct.iso G (stalkSheaf F) ≪≫
    Pi.mapIso (fun x => underlyingSkyscraperIso (geometricPoint x) ((stalk (R := R) x).obj F))

/-- Acyclicity of the abelian skyscraper product implies acyclicity in the
same degree for the underlying abelian sheaf of an injective module sheaf. -/
theorem underlying_H_subsingleton_of_pointProduct (F : Modules (X := X) (R := R)) [Injective F]
    (q : ℕ) (h : Subsingleton ((∏ᶜ fun x : X => (geometricPoint x).skyscraperSheaf
      ((forgetModule (R := R)).obj ((stalk (R := R) x).obj F))).H q)) :
    Subsingleton ((underlying.obj F).H q) := by
  obtain ⟨r, hr⟩ := exists_retraction F
  let G := underlying (X := X) (R := R)
  let e := underlyingPointProductIso F
  let a := G.map (toPointProduct F) ≫ e.hom
  let b := e.inv ≫ G.map r
  have hab : a ≫ b = 𝟙 (G.obj F) := by
    dsimp only [a, b]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp, hr, G.map_id]
  refine ⟨fun x y => ?_⟩
  have he := congrArg (Sheaf.H.map b q) (h.elim (Sheaf.H.map a q x) (Sheaf.H.map a q y))
  simpa only [← Sheaf.H.map_comp_apply, hab, Sheaf.H.map_id_apply] using he

/-- The underlying abelian sheaf of an injective étale module sheaf is
acyclic for global sections. -/
theorem underlying_H_succ (F : Modules (X := X) (R := R)) [Injective F] (q : ℕ) :
    Subsingleton ((underlying.obj F).H (q + 1)) := by
  apply underlying_H_subsingleton_of_pointProduct
  let M := Discrete.functor (fun x : X => (forgetModule (R := R)).obj ((stalk (R := R) x).obj F))
  exact PhilipponEtaleSkyscraperProducts.product_H_succ (fun x : X => x) M q

/-- The underlying abelian sheaf of an injective module sheaf is acyclic
for direct image along every morphism of schemes. -/
theorem underlying_isZero_higherDirectImage {Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules (X := X) (R := R)) [Injective F] (q : ℕ) :
    IsZero (((pushforward f).rightDerived (q + 1)).obj (underlying.obj F)) := by
  obtain ⟨r, hr⟩ := exists_retraction F
  let G := underlying (X := X) (R := R)
  let e := underlyingPointProductIso F
  let a := G.map (toPointProduct F) ≫ e.hom
  let b := e.inv ≫ G.map r
  have hab : a ≫ b = 𝟙 (G.obj F) := by
    dsimp only [a, b]
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp, hr, G.map_id]
  let M := Discrete.functor (fun x : X => (forgetModule (R := R)).obj ((stalk (R := R) x).obj F))
  let H := (pushforward f).rightDerived (q + 1)
  have hZero : IsZero (H.obj _) :=
    PhilipponEtaleSkyscraperProducts.isZero_higherDirectImage_product (fun x : X => x) f M q
  apply (IsZero.iff_id_eq_zero _).mpr
  calc
    𝟙 _ = H.map (a ≫ b) := by rw [hab, H.map_id]
    _ = H.map a ≫ H.map b := H.map_comp _ _
    _ = 0 := by rw [hZero.eq_zero_of_src (H.map b), comp_zero]

end PhilipponEtaleModuleSkyscrapers

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponModuleEtaleNeighborhoodRestriction

universe u
variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- Regard an étale scheme over an étale neighborhood as étale over the base. -/
abbrev along : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (show Etale f from inferInstance)

private def liftObj {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) : Y.Etale :=
  Scheme.Etale.mk (a.left ≫ U.hom)

private def liftIso {V : X.Etale} {U : Y.Etale} (a : V ⟶ (along f).obj U) :
    (along f).obj (liftObj f a) ≅ V :=
  MorphismProperty.Over.isoMk (Iso.refl _)
    ((Category.id_comp _).trans ((MorphismProperty.Over.w a).symm.trans
      (Category.assoc a.left U.hom f).symm))

private theorem coverPreserving : CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (along f) := by
  constructor
  intro W S hS
  rw [← Sieve.ofArrows_category S, Scheme.ofArrows_mem_smallEtaleTopology_iff] at hS
  rw [← Sieve.ofArrows_category S, Sieve.functorPushforward_ofArrows,
    Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact hS

private theorem compatiblePreserving :
    CompatiblePreserving X.smallEtaleTopology (along f) := by
  constructor
  intro F T S z hz U₁ U₂ V a₁ a₂ g₁ g₂ h₁ h₂ h
  let V' := liftObj f a₁
  have hleft := congrArg (fun a => a.left) h
  change a₁.left ≫ g₁.left = a₂.left ≫ g₂.left at hleft
  let b₁ : V' ⟶ U₁ := MorphismProperty.Over.homMk a₁.left rfl trivial
  let b₂ : V' ⟶ U₂ := MorphismProperty.Over.homMk a₂.left (by
    change a₂.left ≫ U₂.hom = a₁.left ≫ U₁.hom
    rw [← MorphismProperty.Over.w g₂, ← MorphismProperty.Over.w g₁,
      ← Category.assoc, ← Category.assoc, hleft]) trivial
  have he : b₁ ≫ g₁ = b₂ ≫ g₂ := MorphismProperty.Over.Hom.ext hleft
  let e := liftIso f a₁
  have hₐ₁ : (along f).map b₁ = e.hom ≫ a₁ :=
    MorphismProperty.Over.Hom.ext (Category.id_comp a₁.left).symm
  have hₐ₂ : (along f).map b₂ = e.hom ≫ a₂ :=
    MorphismProperty.Over.Hom.ext (Category.id_comp a₂.left).symm
  have hz' : F.obj.map ((along f).map b₁).op (z g₁ h₁) =
      F.obj.map ((along f).map b₂).op (z g₂ h₂) := hz b₁ b₂ h₁ h₂ he
  apply (F.obj.mapIso e.op).toEquiv.injective
  simpa only [Iso.op_hom, Iso.toEquiv_fun, F.obj.mapIso_hom, ← Functor.map_comp_apply,
    ← op_comp, ← hₐ₁, ← hₐ₂] using hz'

instance along_isContinuous : (along f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving f) (coverPreserving f)

/-- Restriction to the small étale site of an étale neighborhood. -/
abbrev restrict : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} :=
  (along f).sheafPushforwardContinuous AddCommGrpCat Y.smallEtaleTopology X.smallEtaleTopology

private def restrictAdjunction : restrict f ⊣ pushforward f := by
  let adj : along f ⊣ baseChange f :=
    MorphismProperty.Over.mapPullbackAdj (@Etale) ⊤ f inferInstance trivial
  exact adj.sheafPushforwardContinuous Y.smallEtaleTopology X.smallEtaleTopology

/-- Restriction to an étale neighborhood agrees with the ordinary inverse image. -/
def restrictionIso : restrict f ≅ pullbackSheaves f :=
  (restrictAdjunction f).leftAdjointUniq (pullbackAdjunction f)

section Fibers

variable (W : X.Etale)

private abbrev Lifts := {p : W.left ⟶ Y // p ≫ f = W.hom}
private abbrev Comma := CostructuredArrow (along f).op (op W)

private def liftObject (p : Lifts f W) : Y.Etale := by
  let : Etale (p.val ≫ f) := by rw [p.property]; infer_instance
  let : Etale p.val := Etale.of_comp p.val f
  exact Scheme.Etale.mk p.val

private def liftObjectIso (p : Lifts f W) : (along f).obj (liftObject f W p) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl W.left) ((Category.id_comp _).trans p.property.symm)

private def representative (p : Lifts f W) : Comma f W :=
  CostructuredArrow.mk ((liftObjectIso f W p).inv.op)

private def representatives : Discrete (Lifts f W) ⥤ Comma f W :=
  Discrete.functor (representative f W)

private def liftOfArrow (j : Comma f W) : Lifts f W :=
  ⟨j.hom.unop.left ≫ j.left.unop.hom,
    (Category.assoc _ _ _).trans (MorphismProperty.Over.w j.hom.unop)⟩

private theorem arrow_left_eq {j : Comma f W} {p : Lifts f W}
    (h : j ⟶ representative f W p) : h.left.unop.left = j.hom.unop.left := by
  have he := congrArg (fun a => a.unop.left) (CostructuredArrow.w h)
  change 𝟙 W.left ≫ h.left.unop.left = j.hom.unop.left at he
  exact (Category.id_comp _).symm.trans he

private theorem liftOfArrow_eq {j : Comma f W} {p : Lifts f W}
    (h : j ⟶ representative f W p) : liftOfArrow f W j = p := by
  apply Subtype.ext
  change j.hom.unop.left ≫ j.left.unop.hom = p.val
  rw [← arrow_left_eq f W h]
  exact MorphismProperty.Over.w h.left.unop

private def arrowToRepresentative (j : Comma f W) :
    j ⟶ representative f W (liftOfArrow f W j) := by
  let k : liftObject f W (liftOfArrow f W j) ⟶ j.left.unop :=
    MorphismProperty.Over.homMk j.hom.unop.left rfl trivial
  refine CostructuredArrow.homMk k.op ?_
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  exact Category.id_comp _

private theorem uniqueArrowToRepresentative {j : Comma f W} {p : Lifts f W}
    (a b : j ⟶ representative f W p) : a = b := by
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  exact (arrow_left_eq f W a).trans (arrow_left_eq f W b).symm

private instance representatives_final : (representatives f W).Final where
  out j := by
    let a : StructuredArrow j (representatives f W) :=
      StructuredArrow.mk (arrowToRepresentative f W j)
    apply isConnected_of_isInitial _ (x := a)
    refine IsInitial.ofUniqueHom (fun b => ?_) (fun b h => ?_)
    · let e : a.right = b.right := Discrete.ext (liftOfArrow_eq f W b.hom)
      exact StructuredArrow.homMk (eqToHom e) (uniqueArrowToRepresentative f W _ _)
    · apply StructuredArrow.hom_ext
      exact Subsingleton.elim _ _

end Fibers

section Coefficients

variable {M : Type (u + 1)} [Category.{u} M] [Abelian M]
  [HasColimitsOfSize.{u, u} M] [AB4OfSize.{u} M]

local instance hasPointwiseLeftKanExtension (P : Y.Etaleᵒᵖ ⥤ M) :
    (along f).op.HasPointwiseLeftKanExtension P := by
  intro V
  let W := V.unop
  change HasColimit (CostructuredArrow.proj (along f).op (op W) ⋙ P)
  exact Functor.Final.hasColimit_of_comp (representatives f W)

private abbrev leftKan :
    (Y.Etaleᵒᵖ ⥤ M) ⥤ X.Etaleᵒᵖ ⥤ M :=
  (along f).op.lan

private instance leftKan_preservesMonomorphisms : (leftKan (M := M) f).PreservesMonomorphisms where
  preserves {P Q} α hα := by
    rw [NatTrans.mono_iff_mono_app] at hα ⊢
    intro V
    let W := V.unop
    let L := (along f).op
    let R := representatives f W
    let D := R ⋙ CostructuredArrow.proj L (op W)
    let c (B : Y.Etaleᵒᵖ ⥤ M) : Cocone (D ⋙ B) :=
      ((Functor.LeftExtension.mk _ (L.leftKanExtensionUnit B)).coconeAt (op W)).whisker R
    let hc (B : Y.Etaleᵒᵖ ⥤ M) : IsColimit (c B) :=
      (Functor.Final.isColimitWhiskerEquiv R _).symm
        (L.isPointwiseLeftKanExtensionLeftKanExtensionUnit B (op W))
    let e (B : Y.Etaleᵒᵖ ⥤ M) : ((leftKan f).obj B).obj (op W) ≅ colimit (D ⋙ B) :=
      (hc B).coconePointUniqueUpToIso (colimit.isColimit _)
    have he (B : Y.Etaleᵒᵖ ⥤ M) (j : Discrete (Lifts f W)) :
        (c B).ι.app j ≫ (e B).hom = colimit.ι (D ⋙ B) j :=
      (hc B).comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) j
    let β := Functor.whiskerLeft D α
    have hAt (j : Discrete (Lifts f W)) :
        (c P).ι.app j ≫ ((leftKan f).map α).app (op W) = β.app j ≫ (c Q).ι.app j := by
      let t := R.obj j
      change ((L.lanUnit.app P).app t.left ≫ (L.lan.obj P).map t.hom) ≫
        (L.lan.map α).app (op W) = α.app t.left ≫ ((L.lanUnit.app Q).app t.left ≫
          (L.lan.obj Q).map t.hom)
      rw [Category.assoc, (L.lan.map α).naturality t.hom, ← Category.assoc]
      have hn := NatTrans.congr_app (L.lanUnit.naturality α) t.left
      change α.app t.left ≫ (L.lanUnit.app Q).app t.left =
        (L.lanUnit.app P).app t.left ≫ (L.lan.map α).app (L.obj t.left) at hn
      rw [← hn, Category.assoc]
    have hcomp : ((leftKan f).map α).app (op W) ≫ (e Q).hom =
        (e P).hom ≫ colim.map β := by
      apply (hc P).hom_ext
      intro j
      rw [← Category.assoc, hAt, Category.assoc, he Q, ← Category.assoc, he P]
      exact (colimit.ι_map β j).symm
    let : Mono β := (NatTrans.mono_iff_mono_app _).mpr (fun j => hα (D.obj j))
    let : PreservesFiniteLimits (colim (J := Discrete (Lifts f W)) (C := M)) :=
      HasExactColimitsOfShape.preservesFiniteLimits
    exact mono_of_mono_fac hcomp

/-- Restriction along an étale map preserves injectives with coefficients in an
abelian category with exact coproducts and left exact sheafification. -/
theorem restriction_preservesInjectiveObjects [HasSheafify X.smallEtaleTopology M] :
    ((along f).sheafPushforwardContinuous M Y.smallEtaleTopology
      X.smallEtaleTopology).PreservesInjectiveObjects := by
  let L := Functor.sheafPullbackConstruction.sheafPullback (along f) M
    Y.smallEtaleTopology X.smallEtaleTopology
  have : L.PreservesMonomorphisms := by
    unfold L Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (along f) M
      Y.smallEtaleTopology X.smallEtaleTopology)

end Coefficients

instance along_hasPointwiseLeftKanExtension (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (along f).op.HasPointwiseLeftKanExtension P :=
  hasPointwiseLeftKanExtension f P

instance restrict_preservesInjectiveObjects : (restrict f).PreservesInjectiveObjects :=
  restriction_preservesInjectiveObjects f

instance pullback_preservesInjectiveObjects : (pullbackSheaves f).PreservesInjectiveObjects where
  injective_obj h := Injective.of_iso ((restrictionIso f).app _)
    ((restrict f).injective_obj_of_injective h)

end PhilipponModuleEtaleNeighborhoodRestriction

end

section

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleModuleSkyscrapers (underlying)
namespace PhilipponEtalePrimeTorsionComparison
universe u
variable {X : Scheme.{u}}
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

end PhilipponEtalePrimeTorsionComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtaleModuleSkyscrapers (underlying underlying_H_succ)


namespace PhilipponAffineClosedRestriction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private theorem subsingleton_of_sheaf_iso {X : Scheme.{u}} {F G : Ab X}
    (e : F ≅ G) (q : ℕ) (h : Subsingleton (F.H q)) : Subsingleton (G.H q) := by
  let a := ((Sheaf.functorH X.smallEtaleTopology q).mapIso e).addCommGroupIsoToAddEquiv
  exact ⟨fun x y => a.symm.injective (h.elim (a.symm x) (a.symm y))⟩

/-- Restricting an injective module sheaf to an étale scheme gives an
acyclic underlying abelian sheaf. -/
theorem subsingleton_H_etale {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    {R : Type u} [Ring R] (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) [Injective J]
    (q : ℕ) : Subsingleton (((pullbackSheaves f).obj (underlying.obj J)).H (q + 1)) := by
  let L := (PhilipponModuleEtaleNeighborhoodRestriction.along f).sheafPushforwardContinuous
    (ModuleCat.{u} R) Y.smallEtaleTopology X.smallEtaleTopology
  let : L.PreservesInjectiveObjects := PhilipponModuleEtaleNeighborhoodRestriction.restriction_preservesInjectiveObjects f
  let : Injective (L.obj J) := L.injective_obj_of_injective inferInstance
  let e : underlying.obj (L.obj J) ≅ (pullbackSheaves f).obj (underlying.obj J) :=
    (PhilipponModuleEtaleNeighborhoodRestriction.restrictionIso f).app (underlying.obj J)
  exact subsingleton_of_sheaf_iso e (q + 1) (underlying_H_succ (L.obj J) q)

/-- The vanishing consequence of étale cohomology continuity for a system of affine schemes
mapping compatibly into a fixed base. -/
abbrev AffineLimitVanishing : Prop :=
  ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (_ : IsLimit c)
    {X : Scheme.{u}} (g : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (_ : ∀ i, c.π.app i ≫ g.app i = f) (F : Ab X) (q : ℕ),
    (∀ i, Subsingleton (((pullbackSheaves (g.app i)).obj F).H q)) →
      Subsingleton (((pullbackSheaves f).obj F).H q)

/-- The affine henselian pair comparison for a sheaf killed by one positive integer.
The closed fiber may be presented by a scheme isomorphic to the affine quotient. -/
abbrev HenselianPairComparison : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] (r : A →+* B) [HenselianRing A (RingHom.ker r)]
    (_ : Function.Surjective r) {Z : Scheme.{u}} (e : Z ≅ Spec (.of B))
    (F : Ab (Spec (.of A))) (N : ℕ) (_ : N ≠ 0) (_ : N • 𝟙 F = 0) (q : ℕ),
    Nonempty (AddCommGrpCat.of (F.H q) ≅
      AddCommGrpCat.of (((pullbackSheaves (e.hom ≫ Spec.map (CommRingCat.ofHom r))).obj F).H q))

/-- The affine closed-restriction acyclicity theorem follows from continuity and
the henselian pair comparison. The intervening henselian neighborhood has the
given closed scheme as its closed fiber by construction. -/
theorem subsingleton_H_closed (hLimit : AffineLimitVanishing.{u})
    (hPair : HenselianPairComparison.{u}) {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] (N : ℕ) (hN : N ≠ 0)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) [Injective J]
    (q : ℕ) : Subsingleton (((pullbackSheaves i).obj (underlying.obj J)).H (q + 1)) := by
  let G := underlying.obj J
  let F := InitiallySmall.fromCofilteredInitialModel.{u} (PhilipponHenselianPairNeighborhoods.ExactAffinePointed i)
  let D := F ⋙ PhilipponHenselianPairNeighborhoods.schemes i
  let L := PhilipponHenselianPairNeighborhoods.limitCone i
  let c : Cone D := L.cone.whisker F
  let hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv F L.cone).symm L.isLimit
  let g := F.whiskerLeft (PhilipponHenselianPairNeighborhoods.stagesToBase i)
  let f := PhilipponHenselianPairNeighborhoods.toBase i
  let : ∀ j, IsAffine (D.obj j) := fun j => inferInstanceAs
    (IsAffine ((PhilipponHenselianPairNeighborhoods.schemes i).obj (F.obj j)))
  have hgf (j : _) : c.π.app j ≫ g.app j = f :=
    PhilipponHenselianPairNeighborhoods.projection_toBase i (F.obj j)
  have hH : Subsingleton (((pullbackSheaves f).obj G).H (q + 1)) := by
    apply hLimit D c hc g f hgf G (q + 1)
    intro j
    let : Etale (g.app j) := inferInstanceAs (Etale
      ((PhilipponHenselianPairNeighborhoods.stagesToBase i).app (F.obj j)))
    exact subsingleton_H_etale (g.app j) J q
  let A := PhilipponHenselianPairNeighborhoods.germs i
  let w := PhilipponHenselianPairNeighborhoods.toLimit i
  let r := (PhilipponHenselianPairNeighborhoods.evaluate i).hom
  let : HenselianRing A (RingHom.ker r) := PhilipponHenselianPairNeighborhoods.henselian i
  let : IsAffine Z := isAffine_of_isAffineHom i
  let P := pullbackSheaves f
  let : P.Additive := (PhilipponEtaleSmallSite.pullbackAdjunction f).left_adjoint_additive
  have hKilled : N • 𝟙 (P.obj G) = 0 := by
    calc
      _ = P.map (N • 𝟙 G) := by rw [P.map_nsmul, P.map_id]
      _ = 0 := by rw [PhilipponEtalePrimeTorsionComparison.underlying_killed J, P.map_zero]
  obtain ⟨e⟩ := hPair A Γ(Z, ⊤) r (PhilipponHenselianPairNeighborhoods.evaluation_surjective i)
    Z.isoSpec (P.obj G) N hN hKilled (q + 1)
  have hZG : Subsingleton (((pullbackSheaves w).obj (P.obj G)).H (q + 1)) := by
    let a := e.addCommGroupIsoToAddEquiv
    exact ⟨fun x y => a.symm.injective (hH.elim (a.symm x) (a.symm y))⟩
  have hcomp : w ≫ f = i :=
    (PhilipponHenselianPairNeighborhoods.isPullback_toLimit i).w.trans (Category.id_comp i)
  apply subsingleton_of_sheaf_iso _ _ hZG
  exact (pullbackCompIso f w ≪≫ eqToIso (congrArg pullbackSheaves hcomp)).app G

end PhilipponAffineClosedRestriction

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem solution {X Y : Scheme.{u}} [IsAffine X]
    (i : Y ⟶ X) [IsClosedImmersion i] (N : ℕ) (hN : N.Prime)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u} (ULift.{u} (ZMod N)))) (hJ : Injective J)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hG : G.obj = J.obj ⋙ forget₂ (ModuleCat.{u} (ULift.{u} (ZMod N))) AddCommGrpCat.{u})
    (q : ℕ) : Subsingleton (((PhilipponEtaleSmallSite.pullbackSheaves i).obj G).H (q + 1)) := by
  let := hJ
  have h : G = PhilipponEtaleModuleSkyscrapers.underlying.obj J := ObjectProperty.FullSubcategory.ext hG
  rw [h]
  exact PhilipponAffineClosedRestriction.subsingleton_H_closed AlgebraicGeometry.Scheme.subsingleton_etale_cohomology_of_affine_limit AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_of_henselian_pair i N hN.ne_zero J q

end

end
