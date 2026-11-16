-- Prove2me | Definitions.Def_RPLib_S4_EtShPull
-- name    : RPLib_S4_EtShPull
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:14:38.055277+00:00
-- url     : https://prove2.me/theorems/d3670441-b01c-4024-92dc-eaab3a2eebe8
-- title:
--   Pullback of etale sheaves along a morphism of schemes
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For $f : X \to Y$, base change $V \mapsto V \times_Y X$ is a functor from the small etale site of $Y$ to that of $X$; it preserves finite limits and covering families, so it is continuous, and the pushforward $f_*$ has a left adjoint $f^*$ (a Kan extension along the essentially small affine etale site of $Y$). The stalk of $f^*F$ at a geometric point $\bar s$ of $X$ is the stalk of $F$ at $f \circ \bar s$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose VII; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShStalk

/-!
# S4-EtSheaves, part 2: base change of the small etale site and pullback of etale sheaves

For `f : X ⟶ Y`, `etPull f : Y.Etale ⥤ X.Etale` sends `V → Y` to `V ×_Y X → X`. It preserves finite
limits (hence is representably flat) and preserves covers, so it is continuous for the small etale
topologies. The pushforward `push f` has a left adjoint `pull f` (`f^*`): Kan extension along the
essentially small affine etale site of `Y`. The stalk of `f^*F` at a geometric point `s` of `X` is
the stalk of `F` at `s ≫ f`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- Pointwise description of the covering sieves of the small etale site. -/
theorem mem_smallEtale_iff {Z : Scheme.{u}} (V : Z.Etale) (R : Sieve V) :
    R ∈ Z.smallEtaleTopology V ↔
      ∀ x : V.left, ∃ (W : Z.Etale) (g : W ⟶ V) (w : W.left), R g ∧ g.left w = x := by
  have e := Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
    (P := @Etale) (Q := @Etale) Z le_rfl
  change R ∈ Z.smallGrothendieckTopology (P := @Etale) V ↔ _
  rw [e]
  refine (Scheme.mem_toGrothendieck_smallPretopology (P := @Etale) (Q := @Etale) V R).trans ?_
  constructor
  · intro h x
    obtain ⟨W, g, w, hg, -, hw⟩ := h x
    exact ⟨W, g, w, hg, hw⟩
  · intro h x
    obtain ⟨W, g, w, hg, hw⟩ := h x
    exact ⟨W, g, w, hg, inferInstance, hw⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change of etale `Y`-schemes along `f : X ⟶ Y`. -/
def etPull : Y.Etale ⥤ X.Etale := MorphismProperty.Over.pullback (P := @Etale) (Q := ⊤) f

@[simp] theorem etPull_obj_left (V : Y.Etale) : ((etPull f).obj V).left = pullback V.hom f := rfl

@[simp] theorem etPull_obj_hom (V : Y.Etale) :
    ((etPull f).obj V).hom = pullback.snd V.hom f := rfl

@[simp] theorem etPull_map_left {V W : Y.Etale} (g : V ⟶ W) :
    ((etPull f).map g).left = pullback.lift (pullback.fst V.hom f ≫ g.left)
      (pullback.snd V.hom f) (by simp [pullback.condition]) := rfl

/-- `etPull f` lies over base change of `Y`-schemes. -/
def etPullForgetIso :
    etPull f ⋙ Scheme.Etale.forget X ≅ Scheme.Etale.forget Y ⋙ CategoryTheory.Over.pullback f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro V W g
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

instance : PreservesFiniteLimits (etPull f) := by
  have : PreservesFiniteLimits (etPull f ⋙ Scheme.Etale.forget X) :=
    preservesFiniteLimits_of_natIso (etPullForgetIso f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (etPull f) (Scheme.Etale.forget X)

instance : RepresentablyFlat (etPull f) := flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
/-- A point of `V ×_Y X` lying over a point of `V` hit by `g : W ⟶ V` comes from `W ×_Y X`. -/
theorem etPull_exists_preimage {V W : Y.Etale} (g : W ⟶ V) (w : W.left)
    (z : ((etPull f).obj V).left) (h : g.left w = pullback.fst V.hom f z) :
    ∃ t : ((etPull f).obj W).left, ((etPull f).map g).left t = z := by
  obtain ⟨t, -, ht2⟩ := Scheme.Pullback.exists_preimage_pullback w z h
  have hgw : g.left ≫ V.hom = W.hom := MorphismProperty.Over.w g
  obtain ⟨p, hp1, hp2⟩ : ∃ p : pullback g.left (pullback.fst V.hom f) ⟶ pullback W.hom f,
      p ≫ pullback.fst W.hom f = pullback.fst _ _ ∧
        p ≫ pullback.snd W.hom f = pullback.snd _ _ ≫ pullback.snd V.hom f :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd V.hom f) (by
      rw [← hgw, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition,
        Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hp : p ≫ ((etPull f).map g).left = pullback.snd _ _ := by
    rw [etPull_map_left]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hp1, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, hp2]
  refine ⟨p t, (Scheme.Hom.comp_apply p _ t).symm.trans ?_⟩
  exact (congrArg (fun φ : pullback g.left (pullback.fst V.hom f) ⟶ pullback V.hom f => φ t) hp).trans
    ht2

theorem etPull_coverPreserving :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (etPull f) where
  cover_preserve {V} {R} hR := by
    rw [mem_smallEtale_iff] at hR ⊢
    intro z
    obtain ⟨W, g, w, hg, hw⟩ := hR (pullback.fst V.hom f z)
    obtain ⟨t, ht⟩ := etPull_exists_preimage f g w z hw
    exact ⟨_, (etPull f).map g, t, R.image_mem_functorPushforward (etPull f) hg, ht⟩

instance : (etPull f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact etPull_coverPreserving f

section Sheaves

variable (Λ : Type u) [CommRing Λ]

/-- `etPull f` restricted to affine etale `Y`-schemes. -/
def affPull : Y.AffineEtale ⥤ X.Etale := Scheme.AffineEtale.Spec Y ⋙ etPull f

instance : (affPull f).IsContinuous (Scheme.AffineEtale.topology Y) X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

instance (V : (X.Etale)ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow (affPull f).op V) (ModuleCat.{u} Λ) :=
  hasColimitsOfShape_of_essentiallySmall.{u} _ _

instance (F : (Y.AffineEtale)ᵒᵖ ⥤ ModuleCat.{u} Λ) : (affPull f).op.HasLeftKanExtension F := by
  have : (affPull f).op.HasPointwiseLeftKanExtension F := fun _ => inferInstance
  infer_instance

/-- Pushforward `f_*` of etale sheaves of `Λ`-modules. -/
abbrev push : EtSh Λ X ⥤ EtSh Λ Y :=
  (etPull f).sheafPushforwardContinuous (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology

instance : (push f Λ).IsRightAdjoint := by
  have h1 : ((affPull f).sheafPushforwardContinuous (ModuleCat.{u} Λ)
      (Scheme.AffineEtale.topology Y) X.smallEtaleTopology).IsRightAdjoint := inferInstance
  have h2 : (push f Λ ⋙ (Scheme.AffineEtale.Spec Y).sheafPushforwardContinuous (ModuleCat.{u} Λ)
      (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology).IsRightAdjoint := h1
  exact (Functor.isRightAdjoint_comp_iff_left _ _).1 h2

/-- Pullback `f^*` of etale sheaves of `Λ`-modules: the left adjoint of `f_*`. -/
abbrev pull : EtSh Λ Y ⥤ EtSh Λ X :=
  (etPull f).sheafPullback (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- `f^* ⊣ f_*`. -/
def pullAdj : pull f Λ ⊣ push f Λ := Functor.sheafAdjunctionContinuous _ _ _ _

end Sheaves

section Stalks

/-- The composite geometric point `s ≫ f` of `Y`. -/
def GeomPt.map (s : GeomPt X) : GeomPt Y where
  Ω := s.Ω
  pt := s.pt ≫ f

/-- The fibre functor of `s ≫ f` is the fibre functor of `s` composed with base change. -/
def fiberMapIso (s : GeomPt X) :
    (s.map f).point.fiber ≅ etPull f ⋙ s.point.fiber :=
  Functor.isoWhiskerLeft (Scheme.Etale.forget Y)
      ((Adjunction.compCoyonedaIso (CategoryTheory.Over.mapPullbackAdj f)).app
        (op (CategoryTheory.Over.mk s.pt))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etPullForgetIso f).symm _ ≪≫ Functor.associator _ _ _

instance (s : GeomPt X) : InitiallySmall.{u} (etPull f ⋙ s.point.fiber).Elements := by
  let e : (s.map f).point.fiber.Elements ≌ (etPull f ⋙ s.point.fiber).Elements :=
    (CategoryOfElements.structuredArrowEquivalence _).trans
      ((StructuredArrow.mapNatIso (fiberMapIso f s)).trans
        (CategoryOfElements.structuredArrowEquivalence _).symm)
  have : InitiallySmall.{u} (s.map f).point.fiber.Elements := (s.map f).point.initiallySmall
  exact initiallySmall_of_initial_of_initiallySmall e.functor

/-- The point of `Y`'s site obtained from `s` through `etPull f`. -/
abbrev comapPt (s : GeomPt X) : (Y.smallEtaleTopology).Point :=
  s.point.comap (etPull f) (etPull_coverPreserving f)

/-- The two points of `Y`'s site at `s ≫ f` agree. -/
def comapPtIso (s : GeomPt X) : (s.map f).point ≅ comapPt f s where
  hom := ⟨(fiberMapIso f s).inv⟩
  inv := ⟨(fiberMapIso f s).hom⟩
  hom_inv_id := by ext : 1; exact (fiberMapIso f s).hom_inv_id
  inv_hom_id := by ext : 1; exact (fiberMapIso f s).inv_hom_id

variable (Λ : Type u) [CommRing Λ]

/-- An isomorphism of points gives an isomorphism of the fibre functors on sheaves. -/
def ptIsoSheafFiber {Z : Scheme.{u}} {Φ₁ Φ₂ : (Z.smallEtaleTopology).Point} (e : Φ₁ ≅ Φ₂) :
    Φ₂.sheafFiber (A := ModuleCat.{u} Λ) ≅ Φ₁.sheafFiber where
  hom := e.hom.sheafFiber
  inv := e.inv.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]

/-- **Stalks of a pullback**: `(f^*F)_s ≅ F_(s ≫ f)`, naturally in `F`. -/
def pullStalkIso (s : GeomPt X) : pull f Λ ⋙ s.stalkF Λ ≅ (s.map f).stalkF Λ :=
  (s.point.sheafFiberComapIso (etPull f) (etPull_coverPreserving f) (ModuleCat.{u} Λ)).symm ≪≫
    ptIsoSheafFiber Λ (comapPtIso f s)

end Stalks

end RamanujanPetersson.EtSheaves


