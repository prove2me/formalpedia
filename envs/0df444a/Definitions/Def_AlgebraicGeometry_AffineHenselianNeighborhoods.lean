-- Prove2me | Definitions.Def_AlgebraicGeometry_AffineHenselianNeighborhoods
-- name    : AlgebraicGeometry_AffineHenselianNeighborhoods
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-24T22:55:45.849192+00:00
-- url     : https://prove2.me/theorems/9423b7e8-06c1-454f-9b16-60c3948c2755
-- title:
--   Affine étale neighborhoods and henselization along a closed subscheme
-- statement:
--   Exact affine étale neighborhoods with a chosen lift form a cofiltered system. Its limit is affine and has the prescribed closed fiber, and its coordinate ring is henselian along that fiber.
-- source:
--   Stacks Project, Lemma 59.82.8, https://stacks.math.columbia.edu/tag/0A51.

import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Limits.Preserves.Presheaf
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

set_option maxHeartbeats 1600000

noncomputable section

section

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

end


