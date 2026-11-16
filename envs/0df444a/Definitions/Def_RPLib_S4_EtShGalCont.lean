-- Prove2me | Definitions.Def_RPLib_S4_EtShGalCont
-- name    : RPLib_S4_EtShGalCont
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:17:00.405194+00:00
-- url     : https://prove2.me/theorems/6b7535e7-b8db-4a00-9ed6-20b458897904
-- title:
--   The Galois action on stalks of etale sheaves is continuous
-- statement:
--   Throughout, $X$ is a scheme, $\Lambda$ a commutative ring and $\mathrm{Sh}(X_{\mathrm{et}}, \Lambda)$ the category of sheaves of $\Lambda$-modules on the small etale site of $X$. Residue field extensions of formally unramified morphisms locally of finite type are finite. Every element $v$ of a stalk $F_{\bar x}$ comes from a section over an etale $U \to X$ and a lift $a : \mathrm{Spec}\,\Omega \to U$; $a$ factors through $\mathrm{Spec}\,\kappa(u)$ with $\kappa(u)/\kappa(x)$ finite, so every $\sigma$ fixing the image of $\kappa(u)$ in $\Omega$ fixes $v$. Hence every element of $F_{\bar x}$ has an open stabiliser for the Krull topology: $F_{\bar x}$ is a discrete $\mathrm{Gal}(\kappa(x)^{\mathrm{sep}}/\kappa(x))$-module.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Artin, A. Grothendieck, J.-L. Verdier, Theorie des topos et cohomologie etale des schemas (SGA 4), Lecture Notes in Math. 269, 270, 305, Springer (1972-1973), Expose VIII, Section 2; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter II

import Mathlib
import Definitions.Def_RPLib_S4_EtShGalAct

/-!
# S4-EtSheaves, part 24: the Galois action on stalks is continuous

Residue field extensions of formally unramified morphisms locally of finite type are finite
(`residueField_finite`). Every element `v` of a stalk `F_x̄` comes from a section over an etale `U → X` and a
lift `a : Spec Ω → U`; `a` factors through `Spec κ(u)` with `κ(u)/κ(x)` finite, so every `σ` fixing the image of
`κ(u)` in `Ω` fixes `v`. Hence every element of `F_x̄` has an open stabilizer for the Krull topology
(`exists_open_fix`): `F_x̄` is a discrete `Gal(κ(x)^sep/κ(x))`-module.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

/-- **Residue field extensions of formally unramified morphisms locally of finite type are finite.** -/
theorem residueField_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f.base x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact AlgebraicGeometry.FormallyUnramified.stalkMap f x
  have h : Module.Finite (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) := inferInstance
  have e : algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) = (f.residueFieldMap x).hom := by
    ext r
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    rfl
  have h2 : (algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))).Finite := RingHom.finite_algebraMap.2 h
  change RingHom.Finite (f.residueFieldMap x).hom
  rw [← e]
  exact h2

namespace GeomPt

variable {X : Scheme.{u}} (s : GeomPt X) (Λ : Type u) [CommRing Λ]

/-- A point of the fibre of `s` over `U` as a lift `Spec Ω ⟶ U` over `X`. -/
def liftOf {U : X.Etale} (a : s.point.fiber.obj U) :
    CategoryTheory.Over.mk s.pt ⟶ (Scheme.Etale.forget X).obj U := a

/-- `τ` fixes the lift `a` when `τ ≫ a = a`. -/
theorem autHom_app_eq (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω))
    (hτ : τ ≫ s.pt = s.pt) {U : X.Etale} (a : s.point.fiber.obj U)
    (h : τ ≫ (s.liftOf a).left = (s.liftOf a).left) : (s.autHom τ hτ).hom.app U a = a := by
  change (Over.homMk τ hτ : CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt) ≫ s.liftOf a =
    s.liftOf a
  exact Over.OverMorphism.ext h

/-- The action of `τ` on a germ: `τ^*` sends the germ of `z` at the lift `a` to its germ at `τ ≫ a`. -/
theorem stalkAut_toPresheafFiber (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω))
    (hτ : τ ≫ s.pt = s.pt) (F : EtSh Λ X) (U : X.Etale) (a : s.point.fiber.obj U) (z : F.val.obj (op U)) :
    ((s.stalkAut Λ τ hτ).app F).hom (s.point.toPresheafFiber U a F.val z) =
      s.point.toPresheafFiber U ((s.autHom τ hτ).hom.app U a) F.val z := by
  change (s.point.toPresheafFiber U a F.val ≫ (s.autHom τ hτ).presheafFiber.app F.val).hom z = _
  rw [GrothendieckTopology.Point.Hom.presheafFiber_app,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc (hφ := _)]

/-- If `τ ≫ a = a` then `τ^*` fixes the germ of every section at `a`. -/
theorem stalkAut_fix (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω))
    (hτ : τ ≫ s.pt = s.pt) (F : EtSh Λ X) (U : X.Etale) (a : s.point.fiber.obj U) (z : F.val.obj (op U))
    (h : τ ≫ (s.liftOf a).left = (s.liftOf a).left) :
    ((s.stalkAut Λ τ hτ).app F).hom (s.point.toPresheafFiber U a F.val z) =
      s.point.toPresheafFiber U a F.val z := by
  rw [stalkAut_toPresheafFiber, s.autHom_app_eq τ hτ a h]

end GeomPt

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- The germ at a lift `a` is fixed by every `σ` with `Spec σ ≫ a = a`. -/
theorem galRep_fix (F : EtSh Λ X) (x : X) (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U)
    (z : F.val.obj (op U)) (σ : Gal x)
    (h : galSpec x σ ≫ ((geomPtAt x).liftOf a).left = ((geomPtAt x).liftOf a).left) :
    galRep Λ F x σ ((geomPtAt x).point.toPresheafFiber U a F.val z) =
      (geomPtAt x).point.toPresheafFiber U a F.val z := by
  rw [galRep_apply]
  exact GeomPt.stalkAut_fix (geomPtAt x) Λ _ _ F U a z h

/-- The germ of a section at a lift `a` has an open stabilizer. -/
theorem exists_open_fix_germ (F : EtSh Λ X) (x : X) (U : X.Etale) (a : (geomPtAt x).point.fiber.obj U)
    (z : F.val.obj (op U)) :
    ∃ H : Subgroup (Gal x), IsOpen (H : Set (Gal x)) ∧
      ∀ σ ∈ H, galRep Λ F x σ ((geomPtAt x).point.toPresheafFiber U a F.val z) =
        (geomPtAt x).point.toPresheafFiber U a F.val z := by
  obtain ⟨⟨u, φ⟩, hp⟩ :=
    (Scheme.SpecToEquivOfField (geomPtAt x).Ω U.left).symm.surjective ((geomPtAt x).liftOf a).left
  have hp' : Spec.map φ ≫ U.left.fromSpecResidueField u = ((geomPtAt x).liftOf a).left := hp
  have hw : ((geomPtAt x).liftOf a).left ≫ U.hom = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf a)
  have key : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X).symm
      ⟨U.hom.base u, U.hom.residueFieldMap u ≫ φ⟩ = (geomPtAt x).pt := by
    change Spec.map (U.hom.residueFieldMap u ≫ φ) ≫ X.fromSpecResidueField (U.hom.base u) = _
    rw [Spec.map_comp, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc]
    exact (congrArg (· ≫ U.hom) hp').trans hw
  have hpt : (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt =
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))⟩ :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).apply_symm_apply _
  have key2 : (⟨U.hom.base u, U.hom.residueFieldMap u ≫ φ⟩ :
      Σ y : X, X.residueField y ⟶ CommRingCat.of (geomPtAt x).Ω) =
      (Scheme.SpecToEquivOfField (geomPtAt x).Ω X) (geomPtAt x).pt := by
    rw [← key, Equiv.apply_symm_apply]
  obtain ⟨e, hφ⟩ := Scheme.SpecToEquivOfField_eq_iff.1 (key2.trans hpt)
  have e' : U.hom.base u = x := e
  subst e'
  have hφ' : ∀ r : X.residueField (U.hom.base u),
      φ.hom (U.hom.residueFieldMap u r) =
        algebraMap (X.residueField (U.hom.base u)) (SeparableClosure (X.residueField (U.hom.base u))) r :=
    fun r => congrArg (fun g => g.hom r) hφ
  let : Algebra (X.residueField (U.hom.base u)) (U.left.residueField u) :=
    (U.hom.residueFieldMap u).hom.toAlgebra
  have : Module.Finite (X.residueField (U.hom.base u)) (U.left.residueField u) := residueField_finite U.hom u
  let φ' : U.left.residueField u →ₐ[X.residueField (U.hom.base u)]
      SeparableClosure (X.residueField (U.hom.base u)) :=
    { toRingHom := φ.hom
      commutes' := hφ' }
  have : FiniteDimensional (X.residueField (U.hom.base u)) φ'.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange φ').toLinearEquiv
  refine ⟨φ'.fieldRange.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen _, fun σ hσ => ?_⟩
  apply galRep_fix
  have hfix : ∀ t : U.left.residueField u, σ (φ.hom t) = φ.hom t := fun t =>
    (IntermediateField.mem_fixingSubgroup_iff _ σ).1 hσ (φ.hom t) ⟨t, rfl⟩
  have hc : φ ≫ CommRingCat.ofHom (σ : SeparableClosure (X.residueField (U.hom.base u)) →+*
      SeparableClosure (X.residueField (U.hom.base u))) = φ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    exact hfix t
  have hS : galSpec (U.hom.base u) σ ≫ Spec.map φ = Spec.map φ :=
    (Spec.map_comp φ _).symm.trans (congrArg Spec.map hc)
  rw [← hp']
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.left.fromSpecResidueField u) hS)

/-- **Every element of a stalk has an open stabilizer**: `F_x̄` is a discrete `Gal(κ(x)^sep/κ(x))`-module. -/
theorem exists_open_fix (F : EtSh Λ X) (x : X) (v : stalk Λ F x) :
    ∃ H : Subgroup (Gal x), IsOpen (H : Set (Gal x)) ∧ ∀ σ ∈ H, galRep Λ F x σ v = v := by
  obtain ⟨U, a, z, rfl⟩ := GrothendieckTopology.Point.toPresheafFiber_jointly_surjective
    (A := ModuleCat.{u} Λ) (geomPtAt x).point (P := F.val) v
  exact exists_open_fix_germ Λ F x U a z

end RamanujanPetersson.EtSheaves


