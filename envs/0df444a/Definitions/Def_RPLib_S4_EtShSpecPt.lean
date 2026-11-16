-- Prove2me | Definitions.Def_RPLib_S4_EtShSpecPt
-- name    : RPLib_S4_EtShSpecPt
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:18:11.579125+00:00
-- url     : https://prove2.me/theorems/73cec4ad-2348-4a02-93f7-587f5a381837
-- title:
--   Geometric points of the spectrum of a field
-- statement:
--   Let $X$ be a scheme with $\mathrm{Spec}\,\kappa(x_0) \to X$ an isomorphism, $\Omega$ a separable closure of $\kappa(x_0)$ and $\Gamma = \mathrm{Gal}(\Omega/\kappa(x_0))$, acting on the fibre functor of the geometric point $\bar x_0$ by $a \mapsto a \circ \mathrm{Spec}\,\sigma$. For an etale $X$-scheme $\mathrm{Spec}\,R$ with $R$ a field, $\Gamma$ acts transitively on the lifts of $\bar x_0$ (they are $\kappa(x_0)$-embeddings $R \to \Omega$). Every lift to an etale $U$ comes from the residue-field object $\mathrm{Spec}\,\kappa(u) \to U$, and a finite subextension $E \subseteq \Omega$ gives an etale object $\mathrm{Spec}\,E$ whose base point is fixed exactly by the fixing subgroup of $E$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V, Section 7; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShGalCont

/-!
# S4-EtSheaves, part 29: geometric points of the spectrum of a field

Let `X` be a scheme with `X.fromSpecResidueField x0` an isomorphism ("`X = Spec κ(x0)`"), `Ω` the separable closure
of `κ(x0)` and `Γ = Gal(Ω/κ(x0))`, acting on the fibre functor of `geomPtAt x0` by `a ↦ Spec σ ≫ a` (`galAct`).
For an etale `X`-scheme `Spec R` with `R` a field, `Γ` acts transitively on the fibre (`fiber_transitive`: lifts are
`κ(x0)`-embeddings `R → Ω`, which differ by an automorphism of the normal extension `Ω`). Every fibre element over `U`
comes from the residue-field object `Spec κ(u) → U` (`exists_nbhd`), and a finite subextension `E ⊆ Ω` gives the
etale object `specObj E` whose base point `specPt E` is fixed only by the fixing subgroup of `E`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- Two `K`-embeddings of a field `L` into a normal extension `Ω/K` differ by an automorphism of `Ω`. -/
theorem exists_algEquiv_comp {K L Ω : Type u} [Field K] [Field L] [Field Ω] [Algebra K Ω] [Normal K Ω]
    (φ : K →+* L) (ψ₁ ψ₂ : L →+* Ω) (h₁ : ψ₁.comp φ = algebraMap K Ω) (h₂ : ψ₂.comp φ = algebraMap K Ω) :
    ∃ σ : Ω ≃ₐ[K] Ω, ∀ t : L, σ (ψ₁ t) = ψ₂ t := by
  letI : Algebra K L := φ.toAlgebra
  letI : Algebra L Ω := ψ₁.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun h₁ r).symm
  let ϕ : L →ₐ[K] Ω := { toRingHom := ψ₂, commutes' := fun r => RingHom.congr_fun h₂ r }
  exact ⟨AlgEquiv.ofBijective (ϕ.liftNormal Ω) (Algebra.IsAlgebraic.algHom_bijective _),
    fun t => ϕ.liftNormal_commutes Ω t⟩

/-- A finite separable field extension gives an etale morphism of spectra. -/
theorem etale_specMap_field (K E : Type u) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E] : Etale (Spec.map (CommRingCat.ofHom (algebraMap K E))) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2
    ⟨Algebra.FormallyEtale.of_isSeparable K E, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩)

/-- **The residue field extension of an etale morphism is etale** (finite separable). -/
theorem etale_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X) :
    Etale (Spec.map (f.residueFieldMap x)) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact AlgebraicGeometry.FormallyUnramified.stalkMap f x
  have e : algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) = (f.residueFieldMap x).hom := by
    ext r
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    rfl
  have h2 : (algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))).Etale := RingHom.etale_algebraMap.2
    ⟨Algebra.FormallyEtale.of_isSeparable _ _, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  rw [e] at h2
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).2 h2

/-- A scheme isomorphic to the spectrum of a residue field has one point. -/
theorem subsingleton_of_isIso {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] : Subsingleton X :=
  ⟨fun y z => by
    rw [← Scheme.inv_hom_apply (asIso (X.fromSpecResidueField x0)) y,
      ← Scheme.inv_hom_apply (asIso (X.fromSpecResidueField x0)) z,
      Subsingleton.elim ((asIso (X.fromSpecResidueField x0)).inv y) ((asIso (X.fromSpecResidueField x0)).inv z)]⟩

theorem isIso_fromSpecResidueField {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] (y : X) :
    IsIso (X.fromSpecResidueField y) := by
  haveI := subsingleton_of_isIso x0
  obtain rfl : y = x0 := Subsingleton.elim y x0
  infer_instance

/-- Fibre elements of a geometric point are equal when their underlying morphisms are. -/
theorem fiber_ext {X : Scheme.{u}} (s : GeomPt X) {U : X.Etale} {a b : s.point.fiber.obj U}
    (h : (s.liftOf a).left = (s.liftOf b).left) : a = b := by
  show s.liftOf a = s.liftOf b
  exact Over.OverMorphism.ext h

/-- The Galois action on the fibre functor of `geomPtAt x`: `σ` sends a lift `a` to `Spec σ ≫ a`. -/
def galAct {X : Scheme.{u}} (x : X) (σ : Gal x) : (geomPtAt x).point.fiber ⟶ (geomPtAt x).point.fiber :=
  ((geomPtAt x).autHom (galSpec x σ) (galSpec_comp x σ)).hom

theorem galAct_left {X : Scheme.{u}} (x : X) (σ : Gal x) (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U) :
    ((geomPtAt x).liftOf ((galAct x σ).app U a)).left = galSpec x σ ≫ ((geomPtAt x).liftOf a).left := rfl

theorem galAct_mul {X : Scheme.{u}} (x : X) (σ τ : Gal x) (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U) :
    (galAct x (σ * τ)).app U a = (galAct x σ).app U ((galAct x τ).app U a) := by
  refine fiber_ext _ ?_
  rw [galAct_left, galAct_left, galAct_left, galSpec_mul]
  exact Category.assoc _ _ _

theorem galAct_one {X : Scheme.{u}} (x : X) (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U) :
    (galAct x 1).app U a = a := by
  refine fiber_ext _ ?_
  rw [galAct_left, galSpec_one]
  exact Category.id_comp _

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)]

/-- A lift `Spec ψ` of `geomPtAt x0` through `Spec φ ≫ (Spec κ(x0) ≅ X)` is a `κ(x0)`-embedding: `φ ≫ ψ = ι`. -/
theorem lift_eq {R : CommRingCat.{u}} (φ : X.residueField x0 ⟶ R)
    (ψ : R ⟶ CommRingCat.of (SeparableClosure (X.residueField x0)))
    (h : Spec.map ψ ≫ Spec.map φ ≫ X.fromSpecResidueField x0 = (geomPtAt x0).pt) :
    φ ≫ ψ = CommRingCat.ofHom (algebraMap (X.residueField x0) (SeparableClosure (X.residueField x0))) := by
  apply Spec.map_injective
  apply (cancel_mono (X.fromSpecResidueField x0)).1
  rw [Spec.map_comp, Category.assoc]
  exact h

/-- **Transitivity**: `Gal(Ω/κ(x0))` acts transitively on the fibre of an etale `Spec R → X`, `R` a field. -/
theorem fiber_transitive {L : Type u} [Field L] (h : Spec (CommRingCat.of L) ⟶ X) (hh : Etale h)
    (b₁ b₂ : (geomPtAt x0).point.fiber.obj (MorphismProperty.Over.mk ⊤ h hh)) :
    ∃ σ : Gal x0, (galAct x0 σ).app _ b₁ = b₂ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (h ≫ inv (X.fromSpecResidueField x0))
  have hφ' : Spec.map φ ≫ X.fromSpecResidueField x0 = h := by
    rw [hφ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ : CommRingCat.of L ⟶ CommRingCat.of (SeparableClosure (X.residueField x0)),
      Spec.map ψ = ((geomPtAt x0).liftOf b₁).left := Spec.map_surjective _
  obtain ⟨ψ₂, hψ₂⟩ : ∃ ψ : CommRingCat.of L ⟶ CommRingCat.of (SeparableClosure (X.residueField x0)),
      Spec.map ψ = ((geomPtAt x0).liftOf b₂).left := Spec.map_surjective _
  have e₁ := lift_eq x0 φ ψ₁ (by
    rw [hφ']; exact (congrArg (· ≫ h) hψ₁).trans (Over.w ((geomPtAt x0).liftOf b₁)))
  have e₂ := lift_eq x0 φ ψ₂ (by
    rw [hφ']; exact (congrArg (· ≫ h) hψ₂).trans (Over.w ((geomPtAt x0).liftOf b₂)))
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp (K := X.residueField x0) (L := L)
    (Ω := SeparableClosure (X.residueField x0)) φ.hom ψ₁.hom ψ₂.hom
    (congrArg CommRingCat.Hom.hom e₁) (congrArg CommRingCat.Hom.hom e₂)
  have key : galSpec x0 σ ≫ Spec.map ψ₁ = Spec.map ψ₂ := by
    rw [galSpec, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun t => hσ t))
  exact ⟨σ, fiber_ext _ ((congrArg (galSpec x0 σ ≫ ·) hψ₁).symm.trans (key.trans hψ₂))⟩

include x0 in
theorem etale_res (U : X.Etale) (u : U.left) : Etale (U.left.fromSpecResidueField u ≫ U.hom) := by
  haveI := isIso_fromSpecResidueField x0 (U.hom.base u)
  haveI := etale_residueFieldMap U.hom u
  have e : U.left.fromSpecResidueField u ≫ U.hom =
      Spec.map (U.hom.residueFieldMap u) ≫ X.fromSpecResidueField (U.hom.base u) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := U.hom) (x := u)).symm
  rw [e]
  infer_instance

/-- **Residue-field neighbourhoods**: every fibre element `a` over `U` is the image of a fibre element `b` of an etale
`V ⟶ U` (namely `Spec κ(u) → U`) on whose fibre the Galois group acts transitively. -/
theorem exists_nbhd (U : X.Etale) (a : (geomPtAt x0).point.fiber.obj U) :
    ∃ (V : X.Etale) (g : V ⟶ U) (b : (geomPtAt x0).point.fiber.obj V),
      (geomPtAt x0).point.fiber.map g b = a ∧
      ∀ b' : (geomPtAt x0).point.fiber.obj V, ∃ σ : Gal x0, (galAct x0 σ).app V b = b' := by
  obtain ⟨⟨u, φ⟩, hp⟩ :=
    (Scheme.SpecToEquivOfField (geomPtAt x0).Ω U.left).symm.surjective ((geomPtAt x0).liftOf a).left
  have hp' : Spec.map φ ≫ U.left.fromSpecResidueField u = ((geomPtAt x0).liftOf a).left := hp
  have hw : Spec.map φ ≫ (U.left.fromSpecResidueField u ≫ U.hom) = (geomPtAt x0).pt := by
    rw [← Category.assoc, hp']
    exact Over.w ((geomPtAt x0).liftOf a)
  let V : X.Etale := MorphismProperty.Over.mk ⊤ (U.left.fromSpecResidueField u ≫ U.hom) (etale_res x0 U u)
  let g : V ⟶ U := MorphismProperty.Over.homMk (U.left.fromSpecResidueField u) rfl trivial
  let b : (geomPtAt x0).point.fiber.obj V :=
    (Over.homMk (Spec.map φ) hw : CategoryTheory.Over.mk (geomPtAt x0).pt ⟶ (Scheme.Etale.forget X).obj V)
  refine ⟨V, g, b, fiber_ext _ hp', fun b' =>
    fiber_transitive x0 (L := U.left.residueField u) (U.left.fromSpecResidueField u ≫ U.hom) (etale_res x0 U u) b b'⟩

variable (E : IntermediateField (X.residueField x0) (SeparableClosure (X.residueField x0)))
  [FiniteDimensional (X.residueField x0) E]

theorem etale_specObj : Etale (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x0) E)) ≫
    X.fromSpecResidueField x0) := by
  haveI := etale_specMap_field (X.residueField x0) E
  infer_instance

/-- The etale `X`-scheme `Spec E` of a finite subextension `E` of `Ω/κ(x0)`. -/
def specObj : X.Etale :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x0) E)) ≫
    X.fromSpecResidueField x0) (etale_specObj x0 E)

theorem specPt_w : Spec.map (CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x0) E)) ≫ X.fromSpecResidueField x0 =
      (geomPtAt x0).pt := by
  have e : CommRingCat.ofHom (algebraMap (X.residueField x0) E) ≫
      CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0)) =
      CommRingCat.ofHom (algebraMap (X.residueField x0) (SeparableClosure (X.residueField x0))) := by
    ext r
    rfl
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ X.fromSpecResidueField x0) ((Spec.map_comp _ _).symm.trans (congrArg Spec.map e)))

/-- The base point of `specObj E`: the inclusion `E ⊆ Ω`. -/
def specPt : (geomPtAt x0).point.fiber.obj (specObj x0 E) :=
  (Over.homMk (Spec.map (CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0))))
    (specPt_w x0 E) : CategoryTheory.Over.mk (geomPtAt x0).pt ⟶ (Scheme.Etale.forget X).obj (specObj x0 E))

/-- The stabilizer of the base point `specPt E` lies in the fixing subgroup of `E`. -/
theorem mem_fixingSubgroup_of_galAct {σ : Gal x0} (h : (galAct x0 σ).app _ (specPt x0 E) = specPt x0 E) :
    σ ∈ E.fixingSubgroup := by
  have h1 := congrArg (fun a => ((geomPtAt x0).liftOf a).left) h
  change galSpec x0 σ ≫ Spec.map (CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0))) =
    Spec.map (CommRingCat.ofHom (E.val : E →+* SeparableClosure (X.residueField x0))) at h1
  rw [galSpec, ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro t ht
  exact congrArg (fun g => g.hom ⟨t, ht⟩) h2

/-- Transitivity on the fibre of `specObj E`. -/
theorem specObj_transitive (b : (geomPtAt x0).point.fiber.obj (specObj x0 E)) :
    ∃ σ : Gal x0, (galAct x0 σ).app _ (specPt x0 E) = b :=
  fiber_transitive x0 (L := E) _ (etale_specObj x0 E) (specPt x0 E) b

end RamanujanPetersson.EtSheaves


