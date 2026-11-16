-- Prove2me | Definitions.Def_RPLib_S4_EtShTrans
-- name    : RPLib_S4_EtShTrans
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:23:53.538207+00:00
-- url     : https://prove2.me/theorems/1fe0568b-0b0c-4e1d-82e1-0696b531cc38
-- title:
--   Lifts of a geometric point with the same centre differ by a Galois element
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. For an etale $W \to X$ and two lifts $a, b : \mathrm{Spec}\,\Omega \to W$ of the geometric point $\bar x$ ($\Omega = \kappa(x)^{\mathrm{sep}}$) that hit the same point $w \in W$, there is $\sigma \in \mathrm{Gal}(\Omega/\kappa(x))$ with $b = a \circ \mathrm{Spec}\,\sigma$: both lifts are $\kappa(x)$-embeddings $\kappa(w) \to \Omega$, which differ by an automorphism of the normal extension $\Omega$. Consequently the germs of a section at $a$ and at $b$ differ by the action of $\sigma$, with $\sigma$ independent of the sheaf.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose VIII; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShSpecPt

/-!
# S4-EtSheaves, O10f part a: lifts of `geomPtAt x` with the same centre differ by a Galois element

For an etale `W → X` and two lifts `a, b : Spec Ω → W` of the geometric point `geomPtAt x` (`Ω = κ(x)^sep`) that hit
the same point `w` of `W`, there is `σ ∈ Gal(Ω/κ(x))` with `σ · a = b` (`exists_galAct_eq`): both lifts are
`κ(x)`-embeddings `κ(w) → Ω`, which differ by an automorphism of the normal extension `Ω`. Consequently the germs of a
section at `a` and `b` differ by `σ` (`exists_germ_galRep`), with `σ` independent of the sheaf.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace Trans

variable {X : Scheme.{u}} (x : X)

/-- A morphism `Spec κ(w) ⟶ ...` description of a lift: `Spec α ≫ (Spec κ(w) → W) ≫ W → X = geomPtAt x` forces
`w ↦ x` and `α ∘ κ(x → w) = ι`. -/
theorem lift_cond {W : Scheme.{u}} (g : W ⟶ X) (w : W)
    (α : W.residueField w ⟶ CommRingCat.of (SeparableClosure (X.residueField x)))
    (h : (Spec.map α ≫ W.fromSpecResidueField w) ≫ g = (geomPtAt x).pt) :
    ∃ e : g w = x, g.residueFieldMap w ≫ α =
      (X.residueFieldCongr e).hom ≫ CommRingCat.ofHom (algebraMap (X.residueField x) _) := by
  have h' : Spec.map (g.residueFieldMap w ≫ α) ≫ X.fromSpecResidueField (g w) =
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))) ≫
        X.fromSpecResidueField x := by
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [Category.assoc] at h
    exact h
  have h2 : (⟨g w, g.residueFieldMap w ≫ α⟩ : Σ y : X, X.residueField y ⟶ _) =
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))⟩ :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm.injective h'
  exact Scheme.SpecToEquivOfField_eq_iff.1 h2

/-- The pair form of the transitivity statement. -/
theorem exists_pair {W : Scheme.{u}} (g : W ⟶ X) (w : W)
    (α β : W.residueField w ⟶ CommRingCat.of (SeparableClosure (X.residueField x)))
    (hα : (Spec.map α ≫ W.fromSpecResidueField w) ≫ g = (geomPtAt x).pt)
    (hβ : (Spec.map β ≫ W.fromSpecResidueField w) ≫ g = (geomPtAt x).pt) :
    ∃ σ : Gal x, galSpec x σ ≫ (Spec.map α ≫ W.fromSpecResidueField w) =
      Spec.map β ≫ W.fromSpecResidueField w := by
  obtain ⟨e, he⟩ := lift_cond x g w α hα
  obtain ⟨e', he'⟩ := lift_cond x g w β hβ
  let φ : X.residueField x ⟶ W.residueField w := (X.residueFieldCongr e).inv ≫ g.residueFieldMap w
  have h₁ : α.hom.comp φ.hom = algebraMap (X.residueField x) (SeparableClosure (X.residueField x)) := by
    have : φ ≫ α = CommRingCat.ofHom (algebraMap (X.residueField x) _) := by
      show (X.residueFieldCongr e).inv ≫ g.residueFieldMap w ≫ α = _
      rw [he]
      exact Iso.inv_hom_id_assoc (X.residueFieldCongr e) _
    exact congrArg CommRingCat.Hom.hom this
  have h₂ : β.hom.comp φ.hom = algebraMap (X.residueField x) (SeparableClosure (X.residueField x)) := by
    have : φ ≫ β = CommRingCat.ofHom (algebraMap (X.residueField x) _) := by
      show (X.residueFieldCongr e).inv ≫ g.residueFieldMap w ≫ β = _
      rw [he']
      exact Iso.inv_hom_id_assoc (X.residueFieldCongr e) _
    exact congrArg CommRingCat.Hom.hom this
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp (K := X.residueField x) (L := W.residueField w)
    (Ω := SeparableClosure (X.residueField x)) φ.hom α.hom β.hom h₁ h₂
  refine ⟨σ, ?_⟩
  rw [galSpec, ← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext fun t => hσ t)

/-- A morphism `Spec K ⟶ W` from a field is `Spec α ≫ (Spec κ(w) → W)` with `w` its image point. -/
theorem eq_specMap {K : Type u} [Field K] {W : Scheme.{u}} (l : Spec (CommRingCat.of K) ⟶ W) :
    l = Spec.map (W.descResidueField (Scheme.stalkClosedPointTo l)) ≫
      W.fromSpecResidueField (l (IsLocalRing.closedPoint K)) :=
  ((Scheme.SpecToEquivOfField K W).left_inv l).symm

/-- Two lifts `Spec Ω ⟶ W` of `geomPtAt x` through `g : W ⟶ X` hitting the same point differ by a Galois element. -/
theorem exists_galSpec_comp {W : Scheme.{u}} (g : W ⟶ X)
    (la lb : Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ W)
    (wa : la ≫ g = (geomPtAt x).pt) (wb : lb ≫ g = (geomPtAt x).pt)
    (hab : la (IsLocalRing.closedPoint (SeparableClosure (X.residueField x))) =
      lb (IsLocalRing.closedPoint (SeparableClosure (X.residueField x)))) :
    ∃ σ : Gal x, galSpec x σ ≫ la = lb := by
  have key : ∀ (w w' : W) (α : W.residueField w ⟶ CommRingCat.of (SeparableClosure (X.residueField x)))
      (β : W.residueField w' ⟶ CommRingCat.of (SeparableClosure (X.residueField x))), w = w' →
      (Spec.map α ≫ W.fromSpecResidueField w) ≫ g = (geomPtAt x).pt →
      (Spec.map β ≫ W.fromSpecResidueField w') ≫ g = (geomPtAt x).pt →
      ∃ σ : Gal x, galSpec x σ ≫ (Spec.map α ≫ W.fromSpecResidueField w) =
        Spec.map β ≫ W.fromSpecResidueField w' := by
    intro w w' α β h hα hβ
    subst h
    exact exists_pair x g w α β hα hβ
  have ea := eq_specMap la
  have eb := eq_specMap lb
  obtain ⟨σ, hσ⟩ := key _ _ (W.descResidueField (Scheme.stalkClosedPointTo la))
    (W.descResidueField (Scheme.stalkClosedPointTo lb)) hab
    (by rw [ea] at wa; exact wa) (by rw [eb] at wb; exact wb)
  refine ⟨σ, ?_⟩
  rw [ea, eb]
  exact hσ

/-- **Transitivity on a fibre**: two lifts of `geomPtAt x` to an etale `W` with the same centre differ by a Galois
element. -/
theorem exists_galAct_eq (W : X.Etale) (a b : (geomPtAt x).point.fiber.obj W)
    (hab : ((geomPtAt x).liftOf a).left (IsLocalRing.closedPoint (SeparableClosure (X.residueField x))) =
      ((geomPtAt x).liftOf b).left (IsLocalRing.closedPoint (SeparableClosure (X.residueField x)))) :
    ∃ σ : Gal x, (galAct x σ).app W a = b := by
  obtain ⟨σ, hσ⟩ := exists_galSpec_comp x W.hom ((geomPtAt x).liftOf a).left ((geomPtAt x).liftOf b).left
    (Over.w ((geomPtAt x).liftOf a)) (Over.w ((geomPtAt x).liftOf b)) hab
  exact ⟨σ, fiber_ext _ ((galAct_left x σ W a).trans hσ)⟩

variable (Λ : Type u) [CommRing Λ]

/-- `σ` moves the germ at `a` to the germ at `σ · a`. -/
theorem galRep_germ (F : EtSh Λ X) (σ : Gal x) (W : X.Etale) (a : (geomPtAt x).point.fiber.obj W)
    (z : F.obj.obj (op W)) :
    galRep Λ F x σ ((geomPtAt x).point.toPresheafFiber W a F.obj z) =
      (geomPtAt x).point.toPresheafFiber W ((galAct x σ).app W a) F.obj z := by
  rw [galRep_apply]
  exact GeomPt.stalkAut_toPresheafFiber (geomPtAt x) Λ _ _ F W a z

/-- **Germs at lifts with the same centre** differ by one Galois element, for all sheaves and sections at once. -/
theorem exists_germ_galRep (W : X.Etale) (a b : (geomPtAt x).point.fiber.obj W)
    (hab : ((geomPtAt x).liftOf a).left (IsLocalRing.closedPoint (SeparableClosure (X.residueField x))) =
      ((geomPtAt x).liftOf b).left (IsLocalRing.closedPoint (SeparableClosure (X.residueField x)))) :
    ∃ σ : Gal x, ∀ (F : EtSh Λ X) (z : F.obj.obj (op W)),
      (geomPtAt x).point.toPresheafFiber W b F.obj z =
        galRep Λ F x σ ((geomPtAt x).point.toPresheafFiber W a F.obj z) := by
  obtain ⟨σ, hσ⟩ := exists_galAct_eq x W a b hab
  exact ⟨σ, fun F z => by rw [galRep_germ, hσ]⟩

end Trans

end RamanujanPetersson.EtSheaves


