-- Prove2me | Definitions.Def_RPLib_FX_EtP1_02
-- name    : RPLib_FX_EtP1_02
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:05:08.023425+00:00
-- url     : https://prove2.me/theorems/0b81b5fb-c17c-4b54-ab71-d9bb7268e2b0
-- title:
--   Étale cohomology of the projective line, library file 02 of 34
-- statement:
--   File 02 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_GalAct`: S4-EtSheaves, part 23: the Galois action on stalks
--   * `S4.Def_RP_EtSheaves_GalCont`: S4-EtSheaves, part 24: the Galois action on stalks is continuous
--   * `S4.Def_RP_EtSheaves_SpecPt`: S4-EtSheaves, part 29: geometric points of the spectrum of a field
--   * `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
--   * `S4.Def_RP_EtSheaves_GalEt`: S4-EtSheaves, part O10d-1: Galois covers with trivial inertia are etale (Chase-Harrison-Rosenberg)
--   * `S4.Def_RP_EtSheaves_TorSec`: S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover
--   * `S4.Def_RP_EtSheaves_FV`: S4-EtSheaves, part O10d-2(ii): the sheaf `F_V` of a representation of a Galois group
--   * `S4.Def_RP_EtSheaves_StalkRes`: S4-EtSheaves, part 38: stalks of a restriction, on germs
--   * `S4.Def_RP_EtSheaves_HomConst`: S4-EtSheaves, part 8: the internal Hom out of a constant sheaf
--   * `S4.Def_RP_EtSheaves_Faith`: S4-EtSheaves, part 33 (O10a): the stalk functor is faithful on lisse sheaves over a connected base
--   * `S4.Def_RP_EtPi1_Ram`: S4-EtPi1, O1: trivial inertia gives ramification index one, with no perfectness hypothesis
--   * `S4.Def_RP_EtPi1_Tr`: S4-EtPi1, O2: trivial inertia passes to intermediate fields and to larger base rings
--   * `S4.Def_RP_EtPi1_Ufd`: S4-EtPi1, O4: valuations at prime elements of a UFD, and `N`-th powers
--   * `S4.Def_RP_Kummer_Gal`: S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)
--   * `S4.Def_RP_EtSheaves_Trans`: S4-EtSheaves, O10f part a: lifts of `geomPtAt x` with the same centre differ by a Galois element
--   * `S4.Def_RP_EtSheaves_ConstFix`: S4-EtSheaves, O10c part 3: Galois elements fixing a trivialising lift act trivially
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_01

/-!
# Étale cohomology of the projective line, library file 02 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_GalAct`: S4-EtSheaves, part 23: the Galois action on stalks
* `S4.Def_RP_EtSheaves_GalCont`: S4-EtSheaves, part 24: the Galois action on stalks is continuous
* `S4.Def_RP_EtSheaves_SpecPt`: S4-EtSheaves, part 29: geometric points of the spectrum of a field
* `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
* `S4.Def_RP_EtSheaves_GalEt`: S4-EtSheaves, part O10d-1: Galois covers with trivial inertia are etale (Chase-Harrison-Rosenberg)
* `S4.Def_RP_EtSheaves_TorSec`: S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover
* `S4.Def_RP_EtSheaves_FV`: S4-EtSheaves, part O10d-2(ii): the sheaf `F_V` of a representation of a Galois group
* `S4.Def_RP_EtSheaves_StalkRes`: S4-EtSheaves, part 38: stalks of a restriction, on germs
* `S4.Def_RP_EtSheaves_HomConst`: S4-EtSheaves, part 8: the internal Hom out of a constant sheaf
* `S4.Def_RP_EtSheaves_Faith`: S4-EtSheaves, part 33 (O10a): the stalk functor is faithful on lisse sheaves over a connected base
* `S4.Def_RP_EtPi1_Ram`: S4-EtPi1, O1: trivial inertia gives ramification index one, with no perfectness hypothesis
* `S4.Def_RP_EtPi1_Tr`: S4-EtPi1, O2: trivial inertia passes to intermediate fields and to larger base rings
* `S4.Def_RP_EtPi1_Ufd`: S4-EtPi1, O4: valuations at prime elements of a UFD, and `N`-th powers
* `S4.Def_RP_Kummer_Gal`: S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)
* `S4.Def_RP_EtSheaves_Trans`: S4-EtSheaves, O10f part a: lifts of `geomPtAt x` with the same centre differ by a Galois element
* `S4.Def_RP_EtSheaves_ConstFix`: S4-EtSheaves, O10c part 3: Galois elements fixing a trivialising lift act trivially
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtSheaves_GalAct =====
section

/-!
# S4-EtSheaves, part 23: the Galois action on stalks

An automorphism `τ` of `Spec Ω` over `X` is an endomorphism of the point `s` of the small etale site (lifts
`a ↦ τ ≫ a`), so it acts on the stalk functor (`stalkAut`, contravariantly in `τ`). At the geometric point
`geomPtAt x` (`Ω` a separable closure of `κ(x)`) every `σ ∈ Gal(Ω/κ(x))` gives `Spec σ` over `X`, and
`σ ↦ (Spec σ)^*` is a representation `galRep F x` of `Gal(Ω/κ(x))` on `F_x̄`, natural in `F`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

namespace GeomPt

variable {X : Scheme.{u}} (s : GeomPt X)

variable (Λ : Type u) [CommRing Λ]

end GeomPt

variable {X : Scheme.{u}}

theorem galSpec_comp (x : X) (σ : Gal x) : galSpec x σ ≫ (geomPtAt x).pt = (geomPtAt x).pt := by
  change Spec.map (CommRingCat.ofHom (σ : SeparableClosure (X.residueField x) →+* SeparableClosure (X.residueField x))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))) ≫
        X.fromSpecResidueField x =
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (SeparableClosure (X.residueField x)))) ≫
      X.fromSpecResidueField x
  have e : (σ : SeparableClosure (X.residueField x) →+* SeparableClosure (X.residueField x)).comp
      (algebraMap (X.residueField x) (SeparableClosure (X.residueField x))) =
      algebraMap (X.residueField x) (SeparableClosure (X.residueField x)) := by
    ext a
    simp
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem galSpec_mul (x : X) (σ ρ : Gal x) : galSpec x (σ * ρ) = galSpec x σ ≫ galSpec x ρ := by
  rw [galSpec, galSpec, galSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable (Λ : Type u) [CommRing Λ]

/-- **The Galois representation on a stalk**: `Gal(Ω/κ(x))` acts on `F_x̄`. -/
def galRep (F : EtSh Λ X) (x : X) : Representation Λ (Gal x) (stalk Λ F x) where
  toFun σ := (((geomPtAt x).stalkAut Λ (galSpec x σ) (galSpec_comp x σ)).app F).hom
  map_one' := congrArg (fun t => (t.app F).hom)
    (GeomPt.stalkAut_id (geomPtAt x) Λ (galSpec_comp x 1) (galSpec_one x))
  map_mul' σ ρ := congrArg (fun t => (t.app F).hom)
    (GeomPt.stalkAut_comp (geomPtAt x) Λ (galSpec_comp x σ) (galSpec_comp x ρ) (galSpec_comp x (σ * ρ))
      (galSpec_mul x σ ρ))

theorem galRep_apply (F : EtSh Λ X) (x : X) (σ : Gal x) :
    galRep Λ F x σ = (((geomPtAt x).stalkAut Λ (galSpec x σ) (galSpec_comp x σ)).app F).hom := rfl

/-- **Stalk maps are Galois-equivariant.** -/
theorem galRep_natural {F G : EtSh Λ X} (φ : F ⟶ G) (x : X) (σ : Gal x) :
    (((geomPtAt x).stalkF Λ).map φ).hom ∘ₗ galRep Λ F x σ =
      galRep Λ G x σ ∘ₗ (((geomPtAt x).stalkF Λ).map φ).hom := by
  rw [galRep_apply, galRep_apply, ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, NatTrans.naturality]

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_GalCont =====
section

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

end

end

-- ===== S4.Def_RP_EtSheaves_SpecPt =====
section

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

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)]

variable (E : IntermediateField (X.residueField x0) (SeparableClosure (X.residueField x0)))
  [FiniteDimensional (X.residueField x0) E]

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_A1Hc =====
section

/-!
# S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)

* `lshResIso j G : j_! j^* G ≅ openCut (range j) G` for any open immersion `j` (stalkwise, via `Abelian.monoLift`).
* `cutOpenIso O F : cut (univ ∩ O) F ≅ openCut O F`.
* `A1.hcEquiv : H^n_c(A^1, Λ) ≃+ H^n_c(univ ∩ A^1 ⊆ P^1, Λ_{P^1})` (the compactification `A1.cpt`).
* The comparison `A1.toP1 n : H^n_c(A^1, Λ) →+ H^n(P^1, Λ)` (extension by zero) is injective for `n = 0`, surjective
  for `n = 1` and bijective for `n ≥ 2` (`K` algebraically closed); `A1.hcEquivP1 : H^(n+2)_c(A^1, Λ) ≃+ H^(n+2)(P^1, Λ)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section OpenIm

variable {Λ : Type u} [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

@[reassoc (attr := simp)]
theorem lshToOpenCut_comp (G : EtSh Λ X) :
    lshToOpenCut j G ≫ openCutι Λ j.opensRange G = (lshAdj j Λ).counit.app G :=
  Abelian.monoLift_comp _ _ _

instance isIso_lshToOpenCut (G : EtSh Λ X) : IsIso (lshToOpenCut j G) := by
  rw [isIso_iff_stalk]
  intro x
  by_cases hx : x ∈ Set.range j
  · have h1 := isIso_stalk_openCutι j.opensRange G (geomPtAt x) (center_mem_opensRange j hx)
    obtain ⟨t, ht⟩ := exists_map_eq j (geomPtAt x) (mem_center_geomPtAt hx)
    have h2 : IsIso (((geomPtAt x).stalkF Λ).map ((lshAdj j Λ).counit.app G)) := by
      rw [← ht]
      exact isIso_stalk_counit j Λ t G
    have h3 : IsIso (((geomPtAt x).stalkF Λ).map (lshToOpenCut j G) ≫
        ((geomPtAt x).stalkF Λ).map (openCutι Λ j.opensRange G)) := by
      rw [← Functor.map_comp, lshToOpenCut_comp]
      exact h2
    exact IsIso.of_isIso_comp_right _ (((geomPtAt x).stalkF Λ).map (openCutι Λ j.opensRange G))
  · exact isIso_of_zero_zero _ (lsh_stalk_isZero j Λ _ (not_mem_center_geomPtAt hx) _)
      (isZero_stalk_openCut j.opensRange G _ (center_not_mem_opensRange j hx))

end OpenIm

section OpenCut

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end OpenCut

section A1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

variable [IsAlgClosed K]

end A1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_GalEt =====
section

/-!
# S4-EtSheaves, part O10d-1: Galois covers with trivial inertia are etale (Chase-Harrison-Rosenberg)

Let a finite group `G` act on `B` with `A = B^G` (`IsGaloisGroup G A B`), `A → B` injective and finite, and every
inertia group at a maximal ideal of `B` trivial. Then (Chase-Harrison-Rosenberg, Thm 1.3):

* `exists_chr`: there are `x y : Fin n → B` with `∑ x_i y_i = 1` and `∑ x_i σ(y_i) = 0` for `σ ≠ 1` (`CHR`);
* `projective`: `B` is a projective `A`-module (dual basis `b = ∑ tr(y_i b) x_i`, `sum_trL_smul`);
* `phi_injective`, `phi_surjective`, `torsorEquiv`: `B ⊗_A B ≅ Π_G B`, `b ⊗ b' ↦ (b σ(b'))_σ`;
* `formallyUnramified`, HEADLINE `etale`: `A → B` is etale.

For a `GalCover` `C` this gives `GalCover.etale C : Algebra.Etale A C.B`, the scheme form `GalCover.etale_spec`, and
the torsor isomorphism `GalCover.torsorEquiv C : C.B ⊗[A] C.B ≃ₐ[A] (C.G → C.B)`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves

namespace GalEt

/-- Chase-Harrison-Rosenberg elements: `∑ x_i y_i = 1` and `∑ x_i σ(y_i) = 0` for `σ ≠ 1`. -/
structure CHR {B : Type*} [CommRing B] (G : Type*) [Group G] [MulSemiringAction G B] {n : ℕ} (x y : Fin n → B) :
    Prop where
  one : ∑ i, x i * y i = 1
  ne : ∀ σ : G, σ ≠ 1 → ∑ i, x i * σ • y i = 0

section Pair

variable {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]

/-- Trivial inertia at every maximal ideal: for `σ ≠ 1`, the elements `σ b - b` generate the unit ideal. -/
theorem one_mem_span_sub (hI : ∀ m : Ideal B, m.IsMaximal → m.inertia G = ⊥) {σ : G} (hσ : σ ≠ 1) :
    (1 : B) ∈ Ideal.span (Set.range fun b : B => σ • b - b) := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ ((Ideal.ne_top_iff_one _).mpr h)
  have hmem : σ ∈ m.inertia G := fun x => hle (Ideal.subset_span ⟨x, rfl⟩)
  rw [hI m hm, Subgroup.mem_bot] at hmem
  exact hσ hmem

/-- Reindex a finite family of pairs by `Fin n`. -/
theorem exists_fin_of_fintype {ι : Type*} [Fintype ι] (a b : ι → B) :
    ∃ (n : ℕ) (a' b' : Fin n → B), ∀ f : B → B → B, ∑ i, f (a' i) (b' i) = ∑ i, f (a i) (b i) := by
  classical
  let e := Fintype.equivFin ι
  exact ⟨Fintype.card ι, a ∘ e.symm, b ∘ e.symm, fun f => e.symm.sum_comp (fun i => f (a i) (b i))⟩

/-- CHR (1): for `σ ≠ 1` there are `a b` with `∑ a_j b_j = 1` and `∑ a_j σ(b_j) = 0`. -/
theorem exists_pair (hI : ∀ m : Ideal B, m.IsMaximal → m.inertia G = ⊥) {σ : G} (hσ : σ ≠ 1) :
    ∃ (n : ℕ) (a b : Fin n → B), ∑ i, a i * b i = 1 ∧ ∑ i, a i * σ • b i = 0 := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp (one_mem_span_sub hI hσ)
  have hc' : ∑ i : c.support, c i * σ • (i : B) - ∑ i : c.support, c i * (i : B) = 1 := by
    rw [Finset.sum_coe_sort c.support (fun i => c i * σ • i), Finset.sum_coe_sort c.support (fun i => c i * i),
      ← Finset.sum_sub_distrib]
    simpa only [Finsupp.sum, mul_sub] using hc
  let a : Option c.support → B := fun o => o.elim (∑ i : c.support, c i * σ • (i : B)) fun i => -c i
  let b : Option c.support → B := fun o => o.elim 1 fun i => (i : B)
  obtain ⟨n, a', b', h⟩ := exists_fin_of_fintype a b
  refine ⟨n, a', b', ?_, ?_⟩
  · rw [h (fun u v => u * v), Fintype.sum_option]
    simp only [a, b, Option.elim, neg_mul, Finset.sum_neg_distrib, mul_one]
    linear_combination hc'
  · rw [h (fun u v => u * σ • v), Fintype.sum_option]
    simp only [a, b, Option.elim, neg_mul, Finset.sum_neg_distrib, smul_one, mul_one]
    ring

/-- CHR (2): trivial inertia at the maximal ideals gives CHR elements (product of the pairs over `σ ≠ 1`). -/
theorem exists_chr [Finite G] (hI : ∀ m : Ideal B, m.IsMaximal → m.inertia G = ⊥) :
    ∃ (n : ℕ) (x y : Fin n → B), CHR G x y := by
  classical
  have := Fintype.ofFinite G
  choose n a b hab using fun τ : {τ : G // τ ≠ 1} => exists_pair hI τ.2
  let x : ((τ : {τ : G // τ ≠ 1}) → Fin (n τ)) → B := fun f => ∏ τ, a τ (f τ)
  let y : ((τ : {τ : G // τ ≠ 1}) → Fin (n τ)) → B := fun f => ∏ τ, b τ (f τ)
  obtain ⟨N, x', y', h⟩ := exists_fin_of_fintype x y
  have hprod : ∀ σ : G, ∑ i, x' i * σ • y' i = ∏ τ, ∑ j, a τ j * σ • b τ j := by
    intro σ
    calc ∑ i, x' i * σ • y' i = ∑ f, x f * σ • y f := h (fun u v => u * σ • v)
      _ = ∑ f : ((τ : {τ : G // τ ≠ 1}) → Fin (n τ)), ∏ τ, a τ (f τ) * σ • b τ (f τ) :=
          Finset.sum_congr rfl fun f _ => by
            simp only [x, y, Finset.smul_prod', Finset.prod_mul_distrib]
      _ = ∏ τ, ∑ j, a τ j * σ • b τ j := (Fintype.prod_sum (fun τ j => a τ j * σ • b τ j)).symm
  refine ⟨N, x', y', ⟨?_, fun σ hσ => ?_⟩⟩
  · have h1 := hprod 1
    simp only [one_smul] at h1
    rw [h1]
    exact Finset.prod_eq_one fun τ _ => by simpa only [one_smul] using (hab τ).1
  · rw [hprod σ]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨σ, hσ⟩) (hab ⟨σ, hσ⟩).2

end Pair

section Trace

variable (A : Type*) {B : Type*} (G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [Fintype G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

theorem smul_sum_smul (τ : G) (b : B) : τ • ∑ σ : G, σ • b = ∑ σ : G, σ • b := by
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun _ => rfl

/-- The trace `∑_σ σ(b)`, as an element of `A = B^G`. -/
def trA (b : B) : A :=
  (Algebra.IsInvariant.isInvariant (A := A) (G := G) (∑ σ : G, σ • b) fun τ => smul_sum_smul G τ b).choose

theorem algebraMap_trA (b : B) : algebraMap A B (trA A G b) = ∑ σ : G, σ • b :=
  (Algebra.IsInvariant.isInvariant (A := A) (G := G) (∑ σ : G, σ • b) fun τ => smul_sum_smul G τ b).choose_spec

variable [FaithfulSMul A B]

/-- The trace as an `A`-linear map `B → A`. -/
def trL : B →ₗ[A] A where
  toFun := trA A G
  map_add' b c := FaithfulSMul.algebraMap_injective A B (by
    simp only [map_add, algebraMap_trA, smul_add, Finset.sum_add_distrib])
  map_smul' a b := FaithfulSMul.algebraMap_injective A B (by
    rw [algebraMap_trA, RingHom.id_apply, smul_eq_mul, map_mul, algebraMap_trA, ← Algebra.smul_def,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun σ _ => smul_comm σ a b)

theorem algebraMap_trL (b : B) : algebraMap A B (trL A G b) = ∑ σ : G, σ • b := algebraMap_trA A G b

variable {A G} {n : ℕ} {x y : Fin n → B}

theorem sum_chr (h : CHR G x y) (c : G → B) : ∑ j, (∑ σ : G, σ • y j * c σ) * x j = c 1 := by
  calc _ = ∑ σ : G, c σ * ∑ j, x j * σ • y j := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun j _ => by ring
    _ = c 1 := by
        rw [Finset.sum_eq_single (1 : G) (fun σ _ hσ => by rw [h.ne σ hσ, mul_zero])
          (fun h1 => absurd (Finset.mem_univ _) h1)]
        simp only [one_smul, h.one, mul_one]

/-- The dual basis formula `b = ∑_j tr(y_j b) x_j`. -/
theorem sum_trL_smul (h : CHR G x y) (b : B) : ∑ j, trL A G (y j * b) • x j = b := by
  simp_rw [Algebra.smul_def, algebraMap_trL, smul_mul']
  exact sum_chr h (fun σ => σ • b) |>.trans (one_smul G b)

/-- CHR (3): `B` is a projective `A`-module. -/
theorem projective (h : CHR G x y) : Module.Projective A B := by
  refine Module.Projective.of_split (M := Fin n → A)
    (LinearMap.pi fun j => (trL A G).comp (LinearMap.mulLeft A (y j))) (Fintype.linearCombination A x) ?_
  refine LinearMap.ext fun b => ?_
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply, LinearMap.pi_apply,
    LinearMap.mulLeft_apply, LinearMap.id_apply]
  exact sum_trL_smul h b

end Trace

section Torsor

variable (A : Type*) {B : Type*} (G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- The map `B ⊗_A B → Π_G B`, `b ⊗ b' ↦ (b σ(b'))_σ`. -/
def phi : B ⊗[A] B →ₐ[A] (G → B) :=
  Algebra.TensorProduct.productMap (Pi.constAlgHom A G B)
    (AlgHom.pi fun σ : G => MulSemiringAction.toAlgHom A B σ)

@[simp] theorem phi_tmul (b b' : B) (σ : G) : phi A G (b ⊗ₜ[A] b') σ = b * σ • b' := rfl

variable {A G} [Fintype G] {n : ℕ} {x y : Fin n → B}

/-- A left inverse of `phi`. -/
def psi (x y : Fin n → B) (f : G → B) : B ⊗[A] B := ∑ j, (∑ σ : G, σ • y j * f σ) ⊗ₜ[A] x j

omit [SMulCommClass G A B] in
theorem psi_add (f g : G → B) : psi (A := A) x y (f + g) = psi x y f + psi x y g := by
  simp only [psi, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul]

variable [IsGaloisGroup G A B] [FaithfulSMul A B]

end Torsor

section Etale

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [MulSemiringAction G B] [IsGaloisGroup G A B] [FaithfulSMul A B] [Module.Finite A B]

end Etale

end GalEt

end RamanujanPetersson.EtSheaves

namespace RamanujanPetersson.GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

theorem exists_chr : ∃ (n : ℕ) (x y : Fin n → C.B), EtSheaves.GalEt.CHR C.G x y :=
  EtSheaves.GalEt.exists_chr fun m hm => C.unramified m hm.isPrime

end RamanujanPetersson.GalCover

end

end

-- ===== S4.Def_RP_EtSheaves_TorSec =====
section

/-!
# S4-EtSheaves, part O10d-2(i): sections over `T ×_X Y` for a Galois cover

For a Galois cover `C : GalCover A`, `π : Y = Spec B → X = Spec A` and `T` etale over `Y`, the maps
`ι σ : T → T ×_X Y`, `t ↦ (t, σ_Y t)` (`σ ∈ G`, `σ_Y = Spec σ`) cover `T ×_X Y` by pairwise disjoint sections, so for
every etale sheaf `F` on `X`, restriction is a bijection `F(T ×_X Y) ≅ Π_G F(T)` (`secEquiv`).

* `existsUnique_glue`: gluing for sheaves of modules along a covering family of arrows.
* `exists_eq_comp`: two maps `B → K` to a field that agree on `A` differ by some `σ ∈ G` (from `B ⊗_A B ≅ Π_G B`).
* `eq_of_comp_eq`: `φ ∘ σ = φ ∘ τ` for `φ : B → K` forces `σ = τ` (trivial inertia).
* `sec_cover`, `isEmpty_of_sec`, `existsUnique_sec`, `secEquiv`, `sec_naturality`, `pr_surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

section Glue

universe u

variable {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}}

/-- **Gluing** for sheaves of modules on the small etale site along a covering family of arrows. -/
theorem existsUnique_glue (F : EtSh Λ Z) {U : Z.Etale} {I : Type*} {V : I → Z.Etale} (f : ∀ i, V i ⟶ U)
    (hR : Sieve.ofArrows V f ∈ Z.smallEtaleTopology U) (x : ∀ i, F.obj.obj (op (V i)))
    (hx : ∀ i j (W : Z.Etale) (gi : W ⟶ V i) (gj : W ⟶ V j), gi ≫ f i = gj ≫ f j →
      (F.obj.map gi.op).hom (x i) = (F.obj.map gj.op).hom (x j)) :
    ∃! s, ∀ i, (F.obj.map (f i).op).hom s = x i := by
  have h := (Presieve.isSheafFor_arrows_iff (P := F.obj ⋙ coyoneda.obj (op (ModuleCat.of Λ Λ))) f).1
    ((Presieve.isSheafFor_iff_generate _).2 (F.cond (ModuleCat.of Λ Λ) _ hR))
  obtain ⟨t, ht, hu⟩ := h (fun i => elt (x i)) (fun i j W gi gj e => by
    change elt (x i) ≫ F.obj.map gi.op = elt (x j) ≫ F.obj.map gj.op
    rw [elt_comp, elt_comp, hx i j W gi gj e])
  let t' : ModuleCat.of Λ Λ ⟶ F.obj.obj (op U) := t
  refine ⟨t'.hom 1, fun i => ?_, fun s hs => ?_⟩
  · have h1 : t' ≫ F.obj.map (f i).op = elt (x i) := ht i
    have h2 := congrArg (fun φ : ModuleCat.of Λ Λ ⟶ F.obj.obj (op (V i)) => φ.hom 1) h1
    simpa [elt] using h2
  · have e : elt s = t := hu _ fun i => by
      change elt s ≫ F.obj.map (f i).op = elt (x i)
      rw [elt_comp, hs i]
    change s = t'.hom 1
    rw [← elt_one s]
    exact congrArg (fun φ : ModuleCat.of Λ Λ ⟶ F.obj.obj (op U) => φ.hom 1) e

end Glue

namespace TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

variable {C}

variable (Λ : Type) [CommRing Λ]

end TorSec

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_FV =====
section

/-!
# S4-EtSheaves, part O10d-2(ii): the sheaf `F_V` of a representation of a Galois group

* `eqSh S a b`: for an etale sheaf `S` and families `a b : ι → (S ⟶ S)`, the subsheaf of sections `s` with
  `a i s = b i s` for all `i` (glued in `S`, membership by separatedness: `existsUnique_glueS`, `sep_eq`).
* For a Galois cover `C : GalCover A` (`π : Y = Spec B → X = Spec A`) and a representation `ρ` of `G` on `V`:
  `G` acts on `U ×_X Y` over `X` by `1 × σ_Y` (`tE`, natural in `U`), hence on `SV : U ↦ V_X(U ×_X Y)` (`aS`), and on
  values by `ρ(σ⁻¹)` (`th`, `bS`). `FV C Λ V ρ := eqSh (SV C Λ V) (aS C Λ V) (bS C Λ V ρ)`.
* `sec_tE`: `ι τ ≫ (1 × σ_Y) = ι (τ σ)`; `mem_FV_iff`: for `T` etale over `Y`, a section `s` of `V_X` over `T ×_X Y`
  lies in `F_V(T)` iff `s(τσ) = ρ(σ⁻¹) s(τ)` for all `σ τ`, where `s(τ)` is the restriction of `s` along `ι τ`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

section EqSh

universe u

variable {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}}

theorem map_map_apply (F : EtSh Λ Z) {U V W : Z.Etale} (f : V ⟶ U) (g : W ⟶ V) (s : F.obj.obj (op U)) :
    (F.obj.map g.op).hom ((F.obj.map f.op).hom s) = (F.obj.map (g ≫ f).op).hom s := by
  rw [op_comp, CategoryTheory.Functor.map_comp]
  rfl

theorem app_map {F G : EtSh Λ Z} (φ : F ⟶ G) {U V : Z.Etale} (f : V ⟶ U) (s : F.obj.obj (op U)) :
    (φ.hom.app (op V)).hom ((F.obj.map f.op).hom s) = (G.obj.map f.op).hom ((φ.hom.app (op U)).hom s) :=
  congrArg (fun g => g.hom s) (φ.hom.naturality f.op)

variable (S : EtSh Λ Z) {ι : Type*} (a b : ι → (S ⟶ S))

end EqSh

namespace TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

/-- The constant sheaf `V_X`. -/
abbrev VX (A : Type) [CommRing A] (Λ : Type) [CommRing Λ] (V : Type) [AddCommGroup V] [Module Λ V] :
    EtSh Λ (SX A) :=
  constSh Λ (SX A) (ModuleCat.of Λ V)

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)

variable (Λ : Type) [CommRing Λ] (V : Type) [AddCommGroup V] [Module Λ V]

variable {V} (ρ : Representation Λ C.G V)

/-- `ρ(σ⁻¹)` acting on `V_X`. -/
def th (σ : C.G) : VX A Λ V ⟶ VX A Λ V :=
  (constantSheaf (SX A).smallEtaleTopology (ModuleCat.{0} Λ)).map (ModuleCat.ofHom (ρ σ⁻¹))

variable {C}

end TorSec

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_StalkRes =====
section

/-!
# S4-EtSheaves, part 38: stalks of a restriction, on germs

For an etale `g : U ⟶ X` and a geometric point `t` of `U`, `resFib g t Λ F : (res g F)_t ⟶ F_(t ≫ g)` sends the germ of
`z ∈ F(W → U → X)` at a lift `b : Spec Ω ⟶ W` (over `U`) to the germ of `z` at `b` viewed as a lift over `X`
(`liftX`). It is bijective (`resFib_surjective`: every neighbourhood of `t ≫ g` is refined by one of the form
`W ×_X U`; `resFib_injective`: a neighbourhood over `X` of a lift over `U` is again etale over `U`, `etLift`), so it is
an isomorphism `resFibIso` with an explicit germ formula (`resFib_germ`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] (t : GeomPt U)

/-- A lift of `t` into `W` over `U` is a lift of `t ≫ g` into `W` over `X`. -/
def liftX {W : U.Etale} (b : t.point.fiber.obj W) : (t.map g).point.fiber.obj ((etComp g).obj W) :=
  let b' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W := b
  (Over.homMk b'.left ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) (Over.w b'))) :
    CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj ((etComp g).obj W))

theorem liftX_left {W : U.Etale} (b : t.point.fiber.obj W) :
    (show CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj ((etComp g).obj W) from
      liftX g t b).left = (show CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W from b).left := rfl

theorem liftX_map {W W' : U.Etale} (f : W ⟶ W') (b : t.point.fiber.obj W) :
    liftX g t (t.point.fiber.map f b) = (t.map g).point.fiber.map ((etComp g).map f) (liftX g t b) :=
  Over.OverMorphism.ext rfl

variable (Λ : Type u) [CommRing Λ]

/-- **The germ map** `(res g F)_t ⟶ F_(t ≫ g)`. -/
def resFib (F : EtSh Λ X) : (t.stalkF Λ).obj ((res g Λ).obj F) ⟶ ((t.map g).stalkF Λ).obj F :=
  t.point.presheafFiberDesc (P := ((res g Λ).obj F).obj)
    (fun W b => (t.map g).point.toPresheafFiber ((etComp g).obj W) (liftX g t b) F.obj)
    (fun _ W' f b => ((t.map g).point.toPresheafFiber_w ((etComp g).map f) (liftX g t b) F.obj).trans
      (congrArg (fun a => (t.map g).point.toPresheafFiber ((etComp g).obj W') a F.obj)
        (liftX_map g t f b).symm))

@[reassoc]
theorem germ_resFib (F : EtSh Λ X) (W : U.Etale) (b : t.point.fiber.obj W) :
    t.point.toPresheafFiber W b ((res g Λ).obj F).obj ≫ resFib g t Λ F =
      (t.map g).point.toPresheafFiber ((etComp g).obj W) (liftX g t b) F.obj :=
  GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

theorem resFib_germ (F : EtSh Λ X) (W : U.Etale) (b : t.point.fiber.obj W)
    (z : F.obj.obj (op ((etComp g).obj W))) :
    (resFib g t Λ F).hom (t.point.toPresheafFiber W b ((res g Λ).obj F).obj z) =
      (t.map g).point.toPresheafFiber ((etComp g).obj W) (liftX g t b) F.obj z :=
  congrArg (fun φ => φ.hom z) (germ_resFib g t Λ F W b)

theorem resFib_surjective (F : EtSh Λ X) : Function.Surjective (resFib g t Λ F).hom := by
  intro p
  obtain ⟨W, a, z, rfl⟩ := GrothendieckTopology.Point.toPresheafFiber_jointly_surjective
    (A := ModuleCat.{u} Λ) (t.map g).point (P := F.obj) p
  let a' : CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj W := a
  let T : U.Etale := (etPull g).obj W
  let bl : Spec (CommRingCat.of t.Ω) ⟶ pullback W.hom g := pullback.lift a'.left t.pt (Over.w a')
  let b : t.point.fiber.obj T :=
    (Over.homMk bl (pullback.lift_snd _ _ _) :
      CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj T)
  let fX : (etComp g).obj T ⟶ W := MorphismProperty.Over.homMk (pullback.fst W.hom g) pullback.condition trivial
  have hb : (t.map g).point.fiber.map fX (liftX g t b) = a := by
    change (_ : CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj W) = a'
    exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  refine ⟨t.point.toPresheafFiber T b ((res g Λ).obj F).obj ((F.obj.map fX.op).hom z), ?_⟩
  rw [resFib_germ]
  exact (congrArg (fun φ => φ.hom z) ((t.map g).point.toPresheafFiber_w fX (liftX g t b) F.obj)).trans
    (congrArg (fun a => (t.map g).point.toPresheafFiber W a F.obj z) hb)

theorem resFib_injective (F : EtSh Λ X) : Function.Injective (resFib g t Λ F).hom := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨T, b, z, rfl⟩ := GrothendieckTopology.Point.toPresheafFiber_jointly_surjective
    (A := ModuleCat.{u} Λ) t.point (P := ((res g Λ).obj F).obj) q
  rw [resFib_germ] at hq
  have h0 : (t.map g).point.toPresheafFiber ((etComp g).obj T) (liftX g t b) F.obj z =
      (t.map g).point.toPresheafFiber ((etComp g).obj T) (liftX g t b) F.obj 0 := by
    rw [hq]; exact (map_zero _).symm
  obtain ⟨W, f, y, hy, hz⟩ :=
    ((t.map g).point.toPresheafFiber_eq_iff' ((etComp g).obj T) (liftX g t b) z 0).1 h0
  let b' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj T := b
  let y' : CategoryTheory.Over.mk (t.pt ≫ g) ⟶ (Scheme.Etale.forget X).obj W := y
  have hyl : y'.left ≫ f.left = b'.left := congrArg (fun φ : CategoryTheory.Over.mk (t.pt ≫ g) ⟶
    (Scheme.Etale.forget X).obj ((etComp g).obj T) => φ.left) hy
  let W' : U.Etale := etLift g (W := T) W f.left (MorphismProperty.Over.w f)
  let f' : W' ⟶ T := MorphismProperty.Over.homMk f.left rfl trivial
  let yU : t.point.fiber.obj W' :=
    (Over.homMk y'.left (by
        change y'.left ≫ f.left ≫ T.hom = t.pt
        rw [← Category.assoc, hyl]
        exact Over.w b') :
      CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj W')
  have hyU : t.point.fiber.map f' yU = b := by
    change (_ : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget U).obj T) = b'
    exact Over.OverMorphism.ext hyl
  let e : (etComp g).obj W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl _)
    (by
    change 𝟙 _ ≫ W.hom = (f.left ≫ T.hom) ≫ g
    rw [Category.id_comp, Category.assoc]
    exact (MorphismProperty.Over.w f).symm)
  have hf : f = e.inv ≫ (etComp g).map f' :=
    MorphismProperty.Over.Hom.ext (Category.id_comp f.left).symm
  have hz0 : (F.obj.map ((etComp g).map f').op).hom z = 0 := by
    have h1 : (F.obj.map e.inv.op).hom ((F.obj.map ((etComp g).map f').op).hom z) = 0 := by
      have h2 : (F.obj.map f.op).hom z = 0 := hz.trans (map_zero _)
      rw [hf, op_comp, CategoryTheory.Functor.map_comp] at h2
      exact h2
    have h3 := congrArg (F.obj.map e.hom.op).hom h1
    rw [map_zero] at h3
    refine Eq.trans ?_ h3
    change _ = (F.obj.map e.inv.op ≫ F.obj.map e.hom.op).hom _
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, e.hom_inv_id, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hyU]
  have hw := congrArg (fun φ => φ.hom z) (t.point.toPresheafFiber_w f' yU ((res g Λ).obj F).obj)
  refine hw.symm.trans ?_
  change (t.point.toPresheafFiber W' yU ((res g Λ).obj F).obj).hom
    ((F.obj.map ((etComp g).map f').op).hom z) = 0
  exact (congrArg (t.point.toPresheafFiber W' yU ((res g Λ).obj F).obj).hom hz0).trans (map_zero _)

/-- **Stalks of a restriction along an etale map**, with the germ formula `resFib_germ`. -/
def resFibIso (F : EtSh Λ X) : (t.stalkF Λ).obj ((res g Λ).obj F) ≅ ((t.map g).stalkF Λ).obj F :=
  (LinearEquiv.ofBijective (resFib g t Λ F).hom
    ⟨resFib_injective g t Λ F, resFib_surjective g t Λ F⟩).toModuleIso

theorem resFibIso_hom (F : EtSh Λ X) : (resFibIso g t Λ F).hom = resFib g t Λ F := rfl

theorem resFibIso_inv_germ (F : EtSh Λ X) (W : U.Etale) (b : t.point.fiber.obj W)
    (z : F.obj.obj (op ((etComp g).obj W))) :
    (resFibIso g t Λ F).inv.hom ((t.map g).point.toPresheafFiber ((etComp g).obj W) (liftX g t b) F.obj z) =
      t.point.toPresheafFiber W b ((res g Λ).obj F).obj z := by
  rw [← resFib_germ]
  exact congrArg (fun φ => φ.hom (t.point.toPresheafFiber W b ((res g Λ).obj F).obj z))
    (resFibIso g t Λ F).hom_inv_id

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_HomConst =====
section

/-!
# S4-EtSheaves, part 8: the internal Hom out of a constant sheaf

`Hom(M_X, G) ≅ Hom_Λ(M, G(-))` (`homConstIso`): over `V`, a map `M_V → G|_V` is the same as a map
from the constant presheaf (the sheafification unit restricts to a `J.W`-map on `V`, because
`etComp` is cocontinuous), and a map out of a constant presheaf on `Over V` is its value at the
terminal object `V`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]

/-- `etComp g` is cocontinuous: it is left adjoint to the cover-preserving `etPull g`. -/
instance etComp_isCocontinuous {U : Scheme.{u}} (g : U ⟶ X) [Etale g] :
    (etComp g).IsCocontinuous U.smallEtaleTopology X.smallEtaleTopology :=
  (Adjunction.isCocontinuous_iff_coverPreserving U.smallEtaleTopology X.smallEtaleTopology
    (etCompAdj g)).2 (etPull_coverPreserving g)

/-- Restriction along an etale `g` keeps `J.W` (whiskering by the cocontinuous `etComp g`
preserves locally bijective maps). -/
theorem etW_whisker {U : Scheme.{u}} (g : U ⟶ X) [Etale g] {P Q : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ}
    (f : P ⟶ Q) (hf : X.smallEtaleTopology.W f) :
    U.smallEtaleTopology.W (Functor.whiskerLeft (etComp g).op f) := by
  rw [GrothendieckTopology.W_iff_isLocallyBijective] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  have := h1
  have := h2
  exact ⟨Presheaf.isLocallyInjective_whisker U.smallEtaleTopology X.smallEtaleTopology (etComp g) f,
    Presheaf.isLocallySurjective_whisker U.smallEtaleTopology X.smallEtaleTopology (etComp g) f⟩

variable (M : ModuleCat.{u} Λ) (G : EtSh Λ X)

/-- The constant presheaf `M` on `X.Etale`. -/
abbrev constPre : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := (Functor.const _).obj M

/-- The unit `M ⟶ M_X(V)` of the sheafification. -/
abbrev constUnit (V : X.Etale) : M ⟶ (constSh Λ X M).obj.obj (op V) :=
  (toSheafify X.smallEtaleTopology (constPre M)).app (op V)

/-- The sheafification unit, restricted to `Over V`. -/
def constUnitOver (V : X.Etale) :
    (Functor.const (Over V)ᵒᵖ).obj M ⟶ (Over.forget V).op ⋙ (constSh Λ X M).obj :=
  Functor.whiskerLeft (Over.forget V).op (toSheafify X.smallEtaleTopology (constPre M))

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with the restricted unit is bijective on maps into `G|_V`. -/
theorem bijective_constUnitOver_comp (V : X.Etale) :
    Function.Bijective (fun α : HomOver (constSh Λ X M) G V => constUnitOver M V ≫ α) := by
  let e₀ := presheafHomEquiv (constPre M) G.obj (overOf V)
  let e₁ := presheafHomEquiv (constSh Λ X M).obj G.obj (overOf V)
  have hW := etW_whisker V.hom _ (GrothendieckTopology.W_toSheafify X.smallEtaleTopology (constPre M))
  have hb := hW _ ((res V.hom Λ).obj G).property
  have key : (fun α : HomOver (constSh Λ X M) G V => constUnitOver M V ≫ α) =
      e₀.symm ∘ (fun β => Functor.whiskerLeft (etComp V.hom).op
        (toSheafify X.smallEtaleTopology (constPre M)) ≫ β) ∘ e₁ := by
    funext α
    apply e₀.injective
    rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
    rfl
  rw [key]
  exact e₀.symm.bijective.comp (hb.comp e₁.bijective)

theorem homEquiv_constUnitOver (V : X.Etale) (α : HomOver (constSh Λ X M) G V) :
    (constantPresheafAdj (ModuleCat.{u} Λ) (Over.mkIdTerminal (X := V))).homEquiv
      M ((Over.forget V).op ⋙ G.obj) (constUnitOver M V ≫ α) =
        constUnit M V ≫ α.app (op (Over.mk (𝟙 V))) := by
  rw [Adjunction.homEquiv_unit]
  exact Category.id_comp _

/-- `Hom(M_V, G|_V) ≃ Hom_Λ(M, G(V))`: precompose with the unit, evaluate at the terminal `V`. -/
def homConstEquiv (V : X.Etale) : HomOver (constSh Λ X M) G V ≃ₗ[Λ] (M ⟶ G.obj.obj (op V)) :=
  LinearEquiv.ofBijective
    { toFun := fun α => constUnit M V ≫ α.app (op (Over.mk (𝟙 V)))
      map_add' := fun α β => by
        simp only [NatTrans.app_add]
        exact Preadditive.comp_add _ _ _ _ _ _
      map_smul' := fun c α => by
        simp only [NatTrans.app_smul, RingHom.id_apply]
        exact Linear.comp_smul _ _ _ _ _ _ }
    (by
      have h := ((constantPresheafAdj (ModuleCat.{u} Λ) (Over.mkIdTerminal (X := V))).homEquiv
        M ((Over.forget V).op ⋙ G.obj)).bijective.comp (bijective_constUnitOver_comp M G V)
      have e : (fun α : HomOver (constSh Λ X M) G V => constUnit M V ≫ α.app (op (Over.mk (𝟙 V)))) =
          ((constantPresheafAdj (ModuleCat.{u} Λ) (Over.mkIdTerminal (X := V))).homEquiv
            M ((Over.forget V).op ⋙ G.obj)) ∘ (fun α => constUnitOver M V ≫ α) :=
        funext fun α => (homEquiv_constUnitOver M G V α).symm
      show Function.Bijective (fun α : HomOver (constSh Λ X M) G V =>
        constUnit M V ≫ α.app (op (Over.mk (𝟙 V))))
      rw [e]
      exact h)

theorem homConstEquiv_apply (V : X.Etale) (α : HomOver (constSh Λ X M) G V) :
    homConstEquiv M G V α = constUnit M V ≫ α.app (op (Over.mk (𝟙 V))) := rfl

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Faith =====
section

/-!
# S4-EtSheaves, part 33 (O10a): the stalk functor is faithful on lisse sheaves over a connected base

Germs of constant sections span the stalks of a constant sheaf (`constUnit_germ`); a section of a constant sheaf
has locally constant germs (`germ_constSh`, from local surjectivity of sheafification), so for maps `φ ψ` of constant
sheaves with finite source the locus of geometric points where their stalks agree is locally constant
(`constMap_stalk_locConst`). Transporting along a common etale trivialisation (`exists_common_triv`) gives the same
for `φ ψ : F ⟶ G` with `F` lisse and `G` locally constant (`stalkEq_locConst`). Headline: on a connected `X`, the stalk
functor at ANY geometric point is faithful on such maps (`stalk_faithful`, `stalkF_map_injective`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

attribute [local instance] IsFiltered.isConnected in
/-- `M → M_X(V) → (M_X)_s` (germ at any fibre element) is `constStalkIso⁻¹`. -/
theorem constUnit_germ {X : Scheme.{u}} (s : GeomPt X) (M : ModuleCat.{u} Λ) (V : X.Etale)
    (a : s.point.fiber.obj V) :
    constUnit M V ≫ s.point.toPresheafFiber V a (constSh Λ X M).obj = (constStalkIso Λ s M).inv := by
  have h1 := IsColimit.comp_coconePointUniqueUpToIso_inv
    (s.point.isColimitPresheafFiberCocone ((Functor.const X.Etaleᵒᵖ).obj M))
    (isColimitConstCocone _ M) (op (Functor.elementsMk s.point.fiber V a))
  have h2 : (IsColimit.coconePointUniqueUpToIso
      (s.point.isColimitPresheafFiberCocone ((Functor.const X.Etaleᵒᵖ).obj M))
      (isColimitConstCocone _ M)).inv = s.point.toPresheafFiber V a (constPre M) :=
    (Category.id_comp _).symm.trans h1
  rw [constStalkIso, Iso.trans_inv, h2]
  change _ = s.point.toPresheafFiber V a (constPre M) ≫
    s.point.presheafFiber.map (toSheafify X.smallEtaleTopology (constPre M))
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

namespace GeomPt

variable {Y : Scheme.{u}} (t : GeomPt Y)

/-- The fibre element of `t` over the identity `Y → Y`. -/
def top : t.point.fiber.obj (etId Y) :=
  (Over.homMk t.pt (Category.comp_id t.pt) :
    CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj (etId Y))

/-- The fibre over the identity is a singleton. -/
theorem eq_top (b : t.point.fiber.obj (etId Y)) : b = t.top := by
  let b' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj (etId Y) := b
  have hw : b'.left ≫ 𝟙 Y = t.pt := Over.w b'
  show b' = _
  exact Over.OverMorphism.ext ((Category.comp_id _).symm.trans hw)

/-- A geometric point lifts through an etale `W` at any point over its centre. -/
theorem exists_fiber (W : Y.Etale) (w : W.left) (hw : W.hom w = t.center) :
    Nonempty (t.point.fiber.obj W) := by
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed W.hom t.pt w hw
  exact ⟨(Over.homMk l hl : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj W)⟩

/-- The centre of `t` is in the image of any `W` with a fibre element. -/
theorem center_mem_range {W : Y.Etale} (b : t.point.fiber.obj W) : t.center ∈ Set.range W.hom := by
  let b' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj W := b
  let l : Spec (CommRingCat.of t.Ω) ⟶ W.left := b'.left
  have hw : l ≫ W.hom = t.pt := Over.w b'
  exact ⟨l default, by rw [← Scheme.Hom.comp_apply, hw]; rfl⟩

end GeomPt

theorem iso_inv_eq_zero {A B : ModuleCat.{u} Λ} (e : A ≅ B) (n : B) : e.inv.hom n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := congrArg e.hom.hom h
    rwa [← LinearMap.comp_apply, ← ModuleCat.hom_comp, e.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply,
      map_zero] at this
  · rintro rfl
    exact map_zero _

/-- **Germs of a section of a constant sheaf are locally constant**: near the centre of `t`, the germ of `c` at every
geometric point is the constant germ of one `n ∈ N`. -/
theorem germ_constSh {Y : Scheme.{u}} (N : ModuleCat.{u} Λ) (c : (constSh Λ Y N).obj.obj (op (etId Y)))
    (t : GeomPt Y) :
    ∃ O : Set Y, IsOpen O ∧ t.center ∈ O ∧ ∃ n : N, ∀ t' : GeomPt Y, t'.center ∈ O →
      (t'.point.toPresheafFiber (etId Y) t'.top (constSh Λ Y N).obj).hom c =
        (constStalkIso Λ t' N).inv.hom n := by
  obtain ⟨W, g, ⟨n, hn⟩, b, -⟩ := t.point.jointly_surjective _
    (Presheaf.imageSieve_mem Y.smallEtaleTopology (toSheafify Y.smallEtaleTopology (constPre N)) c) t.top
  have hn' : ((constSh Λ Y N).obj.map g.op).hom c = (constUnit N W).hom n := hn.symm
  refine ⟨Set.range W.hom, W.hom.isOpenMap.isOpen_range, t.center_mem_range b, n, ?_⟩
  rintro t' ⟨w, hw⟩
  obtain ⟨b'⟩ := t'.exists_fiber W w hw
  rw [← t'.eq_top (t'.point.fiber.map g b'), ← GrothendieckTopology.Point.toPresheafFiber_w,
    ModuleCat.hom_comp, LinearMap.comp_apply, hn', ← constUnit_germ t' N W b']
  rfl

/-- The stalk at `t` of `φ : M_Y ⟶ N_Y` on the constant germ of `m` is the germ of `φ(m)`. -/
theorem constMap_germ {Y : Scheme.{u}} {M N : ModuleCat.{u} Λ} (φ : constSh Λ Y M ⟶ constSh Λ Y N)
    (t : GeomPt Y) (m : M) :
    ((t.stalkF Λ).map φ).hom ((constStalkIso Λ t M).inv.hom m) =
      (t.point.toPresheafFiber (etId Y) t.top (constSh Λ Y N).obj).hom
        ((φ.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom m)) := by
  rw [← constUnit_germ t M (etId Y) t.top]
  change (constUnit M (etId Y) ≫ t.point.toPresheafFiber (etId Y) t.top (constSh Λ Y M).obj ≫
    t.point.presheafFiber.map φ.hom).hom m = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

/-- **Maps of constant sheaves with finite source have locally constant stalks**: the predicate "the stalks of `φ`
and `ψ` agree at `t'`" is constant for `t'` centred near the centre of `t`. -/
theorem constMap_stalk_locConst {Y : Scheme.{u}} {M N : ModuleCat.{u} Λ} [Module.Finite Λ M]
    (φ ψ : constSh Λ Y M ⟶ constSh Λ Y N) (t : GeomPt Y) :
    ∃ O : Set Y, IsOpen O ∧ t.center ∈ O ∧ ∀ t' : GeomPt Y, t'.center ∈ O →
      ((t'.stalkF Λ).map φ = (t'.stalkF Λ).map ψ ↔ (t.stalkF Λ).map φ = (t.stalkF Λ).map ψ) := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  obtain ⟨c, hc⟩ : ∃ c : M → (constSh Λ Y N).obj.obj (op (etId Y)), ∀ m, c m =
      (φ.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom m) -
        (ψ.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom m) := ⟨_, fun _ => rfl⟩
  choose O hO hcO n hn using fun m => germ_constSh N (c m) t
  have char : ∀ t' : GeomPt Y, (t'.stalkF Λ).map φ = (t'.stalkF Λ).map ψ ↔
      ∀ m ∈ S, (t'.point.toPresheafFiber (etId Y) t'.top (constSh Λ Y N).obj).hom (c m) = 0 := by
    intro t'
    constructor
    · intro e m _
      have h1 := constMap_germ φ t' m
      have h2 := constMap_germ ψ t' m
      rw [e] at h1
      rw [hc, map_sub, ← h1, ← h2, sub_self]
    · intro h
      rw [← cancel_epi (constStalkIso Λ t' M).inv]
      apply ModuleCat.hom_ext
      refine LinearMap.ext_on hS ?_
      intro m hm
      have := h m (Finset.mem_coe.1 hm)
      rw [hc, map_sub, sub_eq_zero] at this
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        constMap_germ, constMap_germ, this]
  refine ⟨⋂ m ∈ S, O m, isOpen_biInter_finset fun m _ => hO m, Set.mem_iInter₂.2 fun m _ => hcO m,
    fun t' ht' => ?_⟩
  rw [char t', char t]
  refine forall₂_congr fun m hm => ?_
  rw [hn m t' (Set.mem_iInter₂.1 ht' m hm), hn m t (hcO m)]
  exact (iso_inv_eq_zero (constStalkIso Λ t' N) (n m)).trans (iso_inv_eq_zero (constStalkIso Λ t N) (n m)).symm

variable {X : Scheme.{u}}

/-- Lift a geometric point through an etale map at a chosen point over its centre. -/
theorem exists_geomPt_lift {Y : Scheme.{u}} (h : Y ⟶ X) [Etale h] (s : GeomPt X) (y : Y)
    (hy : h y = s.center) : ∃ t : GeomPt Y, t.center = y ∧ t.map h = s := by
  obtain ⟨Ω, pt⟩ := s
  obtain ⟨l, hl, hl2⟩ := Scheme.exists_fac_of_etale_of_isSepClosed h pt y hy
  exact ⟨⟨Ω, l⟩, hl2, by rw [← hl]; rfl⟩

/-- Stalks of `φ, ψ` at `t ≫ h` agree iff the stalks of `h^*φ, h^*ψ` at `t` agree. -/
theorem stalk_eq_iff_pull {Y : Scheme.{u}} (h : Y ⟶ X) (t : GeomPt Y) {F G : EtSh Λ X} (φ ψ : F ⟶ G) :
    ((t.map h).stalkF Λ).map φ = ((t.map h).stalkF Λ).map ψ ↔
      (t.stalkF Λ).map ((pull h Λ).map φ) = (t.stalkF Λ).map ((pull h Λ).map ψ) := by
  rw [← NatIso.naturality_1 (pullStalkIso h Λ t) φ, ← NatIso.naturality_1 (pullStalkIso h Λ t) ψ,
    Functor.comp_map, Functor.comp_map]
  refine ⟨fun e => (Iso.cancel_iso_hom_right _ _ ((pullStalkIso h Λ t).app G)).1 ?_, fun e => by rw [e]⟩
  simpa using e

/-- A lisse `F` and a locally constant `G` are constant on one etale neighbourhood of any point. -/
theorem exists_common_triv {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLocConst Λ G) (x : X) :
    ∃ (Y : Scheme.{u}) (h : Y ⟶ X) (_ : Etale h) (y : Y), h y = x ∧
      ∃ (M N : ModuleCat.{u} Λ), Module.Finite Λ M ∧
        Nonempty ((pull h Λ).obj F ≅ constSh Λ Y M) ∧ Nonempty ((pull h Λ).obj G ≅ constSh Λ Y N) := by
  obtain ⟨U, v, hv, M, hM, ⟨eF⟩⟩ := hF x
  obtain ⟨W, w, hw, N, ⟨eG⟩⟩ := hG.pull U.hom v
  refine ⟨W.left, W.hom ≫ U.hom, inferInstance, w, by rw [Scheme.Hom.comp_apply, hw, hv], M, N, hM,
    ⟨(pullCompIso Λ W.hom U.hom).app F ≪≫ (pull W.hom Λ).mapIso eF ≪≫ pullConst Λ W.hom M⟩,
    ⟨(pullCompIso Λ W.hom U.hom).app G ≪≫ eG⟩⟩

/-- **Agreement of stalk maps is locally constant** for `φ ψ : F ⟶ G`, `F` lisse, `G` locally constant. -/
theorem stalkEq_locConst {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLocConst Λ G) (φ ψ : F ⟶ G)
    (s : GeomPt X) :
    ∃ O : Set X, IsOpen O ∧ s.center ∈ O ∧ ∀ s' : GeomPt X, s'.center ∈ O →
      ((s'.stalkF Λ).map φ = (s'.stalkF Λ).map ψ ↔ (s.stalkF Λ).map φ = (s.stalkF Λ).map ψ) := by
  obtain ⟨Y, h, hh, y, hy, M, N, hM, ⟨eF⟩, ⟨eG⟩⟩ := exists_common_triv hF hG s.center
  obtain ⟨t, ht, rfl⟩ := exists_geomPt_lift h s y hy
  have key : ∀ t' : GeomPt Y, ((t'.map h).stalkF Λ).map φ = ((t'.map h).stalkF Λ).map ψ ↔
      (t'.stalkF Λ).map (eF.inv ≫ (pull h Λ).map φ ≫ eG.hom) =
        (t'.stalkF Λ).map (eF.inv ≫ (pull h Λ).map ψ ≫ eG.hom) := fun t' => by
    rw [stalk_eq_iff_pull]
    simp only [Functor.map_comp, cancel_epi]
    exact (Iso.cancel_iso_hom_right _ _ ((t'.stalkF Λ).mapIso eG)).symm
  obtain ⟨O, hO, hyO, hc⟩ := constMap_stalk_locConst (eF.inv ≫ (pull h Λ).map φ ≫ eG.hom)
    (eF.inv ≫ (pull h Λ).map ψ ≫ eG.hom) t
  have hcen : ∀ t' : GeomPt Y, (t'.map h).center = h t'.center := fun t' =>
    Scheme.Hom.comp_apply t'.pt h default
  refine ⟨h '' O, h.isOpenMap O hO, ⟨t.center, hyO, (hcen t).symm⟩, ?_⟩
  rintro s' ⟨y', hy'O, hy'⟩
  obtain ⟨t', ht', rfl⟩ := exists_geomPt_lift h s' y' hy'
  rw [key, key]
  exact hc t' (ht' ▸ hy'O)

/-- **Faithfulness of the fibre functor on lisse sheaves (O10a)**: on a connected `X`, maps `φ ψ : F ⟶ G` (`F` lisse,
`G` locally constant) with the same stalk map at one geometric point `s` are equal. -/
theorem stalk_faithful [PreconnectedSpace X] {F G : EtSh Λ X} (hF : IsLisse Λ F) (hG : IsLocConst Λ G)
    {φ ψ : F ⟶ G} (s : GeomPt X) (h : (s.stalkF Λ).map φ = (s.stalkF Λ).map ψ) : φ = ψ := by
  have hf : IsLocallyConstant
      (fun x : X => ((geomPtAt x).stalkF Λ).map φ = ((geomPtAt x).stalkF Λ).map ψ) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨O, hO, hxO, hc⟩ := stalkEq_locConst hF hG φ ψ (geomPtAt x)
    refine ⟨O, hO, (center_geomPtAt x) ▸ hxO, fun x' hx' => propext (hc (geomPtAt x') ?_)⟩
    rw [center_geomPtAt]
    exact hx'
  have h0 : ((geomPtAt s.center).stalkF Λ).map φ = ((geomPtAt s.center).stalkF Λ).map ψ := by
    obtain ⟨O, -, hsO, hc⟩ := stalkEq_locConst hF hG φ ψ s
    exact (hc (geomPtAt s.center) (by rw [center_geomPtAt]; exact hsO)).2 h
  exact hom_ext_stalk Λ fun x => (hf.apply_eq_of_preconnectedSpace x s.center).mpr h0

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtPi1_Ram =====
section

/-!
# S4-EtPi1, O1: trivial inertia gives ramification index one, with no perfectness hypothesis

Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` needs a perfect residue field at the base prime. The residue fields
of `F[x₁, …, xₙ]` at height-one primes are not perfect for `n ≥ 2`, so here:

* `card_stabilizer_le`: `|D_P| ≤ |I_P| · f(P|p)` for any Galois `R → S` (`S/R` finite): the decomposition group modulo
  inertia is `Aut(κ(P)/κ(p))` (`IsFractionRing.stabilizerQuotientInertiaEquiv`, no separability needed), and
  `|Aut| ≤ [κ(P) : κ(p)]` (`AlgEquiv.card_le`).
* `ramificationIdxIn_eq_one_of_inertia_eq_bot`: if `I_P = ⊥` then `e(p) = 1` (fundamental identity
  `#primes · e · f = |G|` and orbit-stabilizer `#primes · |D_P| = |G|` give `e f = |D_P| ≤ f`).
* `dvd_log_valuation_of_inertia`: over a Dedekind `R` with fraction field `K`, for `L/K` finite Galois whose inertia
  groups on `integralClosure R L` are all trivial: `α ∈ L`, `α ^ N = a ∈ K` ⟹ `N ∣ v(a)` at every place `v` of `R`.
-/

set_option autoImplicit false

open IsDedekindDomain

namespace RamanujanPetersson
namespace EtPi1

open scoped Pointwise

section Ram

variable {R S G : Type} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

attribute [local instance] Ideal.Quotient.field in
/-- `|D_P| ≤ |I_P| · f(P|p)`, with no separability hypothesis on the residue field extension. -/
theorem card_stabilizer_le [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] :
    Nat.card (MulAction.stabilizer G P) ≤ Nat.card (P.inertia G) * P.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  have : Module.Finite p.ResidueField P.ResidueField := inferInstance
  have hidx : Subgroup.index _ = _ := Nat.card_congr
    (IsFractionRing.stabilizerQuotientInertiaEquiv G p P p.ResidueField P.ResidueField).toEquiv
  have hle : Nat.card Gal(P.ResidueField/p.ResidueField) ≤
      Module.finrank p.ResidueField P.ResidueField := by
    exact Nat.card_eq_fintype_card.trans_le (AlgEquiv.card_le (F := p.ResidueField) (K := P.ResidueField))
  have hst : Nat.card (MulAction.stabilizer G P) =
      Nat.card (P.inertia G) * Nat.card Gal(P.ResidueField/p.ResidueField) := by
    rw [← hidx, ← ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv,
      AddSubgroup.subgroupOf_inertia]
  rw [hst, Ideal.inertiaDeg_eq p P]
  exact Nat.mul_le_mul_left _ hle

/-- **Trivial inertia gives ramification index one** (no perfectness of residue fields). -/
theorem ramificationIdxIn_eq_one_of_inertia_eq_bot [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] [FaithfulSMul R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    [P.LiesOver p] (h : P.inertia G = ⊥) : p.ramificationIdxIn S = 1 := by
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  have horb : (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hle := card_stabilizer_le (G := G) p P
  rw [h, Subgroup.card_bot, one_mul, ← Ideal.inertiaDegIn_eq_inertiaDeg p P G] at hle
  have hG : 0 < Nat.card G := Nat.card_pos
  have hn : (p.primesOver S).ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at horb
    omega
  have hf : p.inertiaDegIn S ≠ 0 := Ideal.inertiaDegIn_ne_zero (G := G)
  have he : p.ramificationIdxIn S ≠ 0 := Ideal.ramificationIdxIn_ne_zero (G := G)
  have hst : Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) (horb.trans hfund.symm)
  rw [hst] at hle
  have h1 : p.ramificationIdxIn S ≤ 1 :=
    (Nat.mul_le_mul_right_iff (Nat.pos_of_ne_zero hf)).1 (by simpa using hle)
  omega

end Ram

section Val

variable (R K L : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L]

/-- Every inertia group of `Gal(L/K)` acting on the integral closure of `R` in `L` is trivial. -/
def InertiaTrivial : Prop :=
  ∀ Q : Ideal (integralClosure R L), Q.IsPrime → Q.inertia (L ≃ₐ[K] L) = ⊥

include K in
omit [IsDedekindDomain R] [FiniteDimensional K L] [IsGalois K L] in
theorem algebraMap_integralClosure_injective :
    Function.Injective (algebraMap R (integralClosure R L)) := by
  intro a b h
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  exact hinj (by simpa using congrArg Subtype.val h)

theorem exists_heightOne_under {B : Type} [CommRing B] [IsDedekindDomain B] [Algebra R B]
    [Module.IsTorsionFree R B] [Algebra.IsIntegral R B] (v : HeightOneSpectrum R) :
    ∃ w : HeightOneSpectrum B, w.under R = v := by
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) v.asIdeal ⊥ (by
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (Module.isTorsionFree_iff_algebraMap_injective.1 inferInstance)]
    exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (Module.isTorsionFree_iff_algebraMap_injective.1 inferInstance)]
  exact ⟨⟨Q, hQ, hQ0⟩, HeightOneSpectrum.ext hQv⟩

/-- **Kummer radicals in an extension with trivial inertia have `N`-divisible valuations** (Dedekind base, no
perfectness hypothesis). -/
theorem dvd_log_valuation_of_inertia (hI : InertiaTrivial R K L) {N : ℕ} {α : L} {a : K}
    (hα : α ^ N = algebraMap K L a) (v : HeightOneSpectrum R) :
    (N : ℤ) ∣ WithZero.log (v.valuation K a) := by
  have : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := R) K L
  have : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L (integralClosure R L)
  have : IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) R (integralClosure R L) K L
  have : Module.IsTorsionFree R (integralClosure R L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_integralClosure_injective R K L)
  have : FaithfulSMul R (integralClosure R L) :=
    (faithfulSMul_iff_algebraMap_injective R _).2 (algebraMap_integralClosure_injective R K L)
  have : IsDedekindDomain (integralClosure R L) :=
    integralClosure.isDedekindDomain (A := R) (K := K) (L := L)
  have : Module.Flat R (integralClosure R L) := inferInstance
  obtain ⟨w, rfl⟩ := exists_heightOne_under R (B := integralClosure R L) v
  have : w.asIdeal.LiesOver (w.under R).asIdeal := ⟨rfl⟩
  have he : (w.under R).asIdeal.ramificationIdx' w.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under R).ne_bot,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx (w.under R).asIdeal w.asIdeal (L ≃ₐ[K] L)]
    exact ramificationIdxIn_eq_one_of_inertia_eq_bot (G := L ≃ₐ[K] L) _ w.asIdeal
      (hI w.asIdeal w.isPrime)
  have hval := HeightOneSpectrum.valuation_liesOver L (w.under R) w a
  rw [he, pow_one] at hval
  rw [hval, ← hα, map_pow, WithZero.log_pow]
  exact ⟨_, nsmul_eq_mul _ _⟩

end Val

end EtPi1
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtPi1_Tr =====
section

/-!
# S4-EtPi1, O2: trivial inertia passes to intermediate fields and to larger base rings

* `inertia_eq_bot_of_tower`: `K ⊆ K' ⊆ L`, `A → R'` with `A → R' → L` and `R' → K' → L` compatible: if every inertia
  group of `Gal(L/K)` on `integralClosure A L` is trivial, then every inertia group of `Gal(L/K')` on
  `integralClosure R' L` is trivial (an inertia element of `Gal(L/K')` restricts to an inertia element of `Gal(L/K)` at
  the prime `Q' ∩ integralClosure A L`).
* `inertia_eq_bot_of_unramSet`: the same for `L ∈ unramSet A K` (input of `dvd_log_valuation_of_inertia`, `EtPi1_Ram`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace EtPi1

section Tower

variable {A K L : Type} [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]
  {K' R' : Type} [Field K'] [CommRing R'] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]
  [Algebra A R'] [Algebra R' L] [IsScalarTower A R' L] [Algebra R' K'] [IsScalarTower R' K' L]

/-- The inclusion `integralClosure A L → integralClosure R' L`. -/
def closureIncl : integralClosure A L →+* integralClosure R' L where
  toFun x := ⟨(x : L), x.2.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem closureIncl_coe (x : integralClosure A L) :
    ((closureIncl (A := A) (L := L) (R' := R') x : integralClosure R' L) : L) = x := rfl

/-- **Trivial inertia passes up a tower.** -/
theorem inertia_eq_bot_of_tower
    (h : ∀ Q : Ideal (integralClosure A L), Q.IsPrime → Q.inertia (L ≃ₐ[K] L) = ⊥)
    (Q' : Ideal (integralClosure R' L)) (hQ' : Q'.IsPrime) : Q'.inertia (L ≃ₐ[K'] L) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  have hQ : (Q'.comap (closureIncl (A := A) (L := L) (R' := R'))).IsPrime := Ideal.comap_isPrime _ Q'
  have hmem : σ.restrictScalars K ∈
      (Q'.comap (closureIncl (A := A) (L := L) (R' := R'))).inertia (L ≃ₐ[K] L) := by
    intro x
    show _ ∈ Q'.comap _
    rw [Ideal.mem_comap]
    have hx : closureIncl (A := A) (L := L) (R' := R') ((σ.restrictScalars K) • x - x) =
        σ • closureIncl (A := A) (L := L) (R' := R') x - closureIncl x := by
      apply Subtype.ext
      simp [AlgEquiv.smul_def]
    rw [hx]
    exact hσ (closureIncl x)
  rw [h _ hQ, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  ext y
  exact DFunLike.congr_fun hmem y

end Tower

section UnramSet

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/-- **Unramified subextensions have trivial inertia over intermediate fields and larger base rings**: for
`L ∈ unramSet A K`, any `K → K' → L` and any `A → R' → K'` (compatible), every inertia group of `Gal(L/K')` on
`integralClosure R' L` is trivial. -/
theorem inertia_eq_bot_of_unramSet {L : IntermediateField K (AlgebraicClosure K)} (hL : L ∈ unramSet A K)
    {K' R' : Type} [Field K'] [CommRing R'] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]
    [Algebra A R'] [Algebra R' L] [IsScalarTower A R' L] [Algebra R' K'] [IsScalarTower R' K' L]
    (Q' : Ideal (integralClosure R' L)) (hQ' : Q'.IsPrime) : Q'.inertia (L ≃ₐ[K'] L) = ⊥ :=
  inertia_eq_bot_of_tower (A := A) (K := K) hL.2.2 Q' hQ'

end UnramSet

end EtPi1
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtPi1_Ufd =====
section

/-!
# S4-EtPi1, O4: valuations at prime elements of a UFD, and `N`-th powers

* `exists_associated_pow_of_dvd_multiplicity`: in a UFD, if `N ∣ multiplicity π f` for every prime `π`, then `f` is
  associated to an `N`-th power (`normalizedFactors f = N • t`).
* `exists_eq_unit_mul_pow`: for `a ≠ 0` in the fraction field `K` of a UFD `R`, if `N` divides
  `ord_π(den a) - ord_π(num a)` for every prime `π`, then `a = u · b ^ N` with `u ∈ Rˣ`, `b ∈ K` (the reduced fraction
  `num/den` has coprime parts, so `N` divides both orders).
* `isDedekindDomain_atPrime`: for `R` noetherian and `π ≠ 0` with `(π)` prime, `D = R_(π)` is a Dedekind domain (a
  noetherian local domain with principal maximal ideal, `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`).
* `place π D hπ`: the closed point of `Spec D` as a height-one prime; `log_intValuation_place`:
  `log v(f) = -ord_π(f)` for `f ∈ R`, and `log_valuation_place`: `log v(a) = ord_π(den a) - ord_π(num a)` for `a ∈ K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsLocalRing IsDedekindDomain

namespace RamanujanPetersson
namespace EtPi1

section Pow

variable {R : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- In a UFD, an element whose multiplicities are all divisible by `N` is associated to an `N`-th power. -/
theorem exists_associated_pow_of_dvd_multiplicity {f : R} (hf : f ≠ 0) {N : ℕ}
    (h : ∀ π : R, Prime π → N ∣ multiplicity π f) : ∃ d : R, Associated (d ^ N) f := by
  classical
  let _ : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  set s := UniqueFactorizationMonoid.normalizedFactors f with hs
  have hc : ∀ x ∈ s, N ∣ s.count x := by
    intro x hx
    have hirr : Irreducible x := UniqueFactorizationMonoid.irreducible_of_normalized_factor x hx
    have hnorm : normalize x = x := UniqueFactorizationMonoid.normalize_normalized_factor x hx
    rw [← hnorm, ← UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hirr hf]
    exact h x (UniqueFactorizationMonoid.prime_of_normalized_factor x hx)
  refine ⟨(∑ x ∈ s.toFinset, (s.count x / N) • ({x} : Multiset R)).prod, ?_⟩
  rw [← Multiset.prod_nsmul]
  have hst : N • ∑ x ∈ s.toFinset, (s.count x / N) • ({x} : Multiset R) = s := by
    rw [Finset.smul_sum]
    conv_rhs => rw [← Multiset.toFinset_sum_count_nsmul_eq s]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [smul_smul, Nat.mul_div_cancel' (hc x (Multiset.mem_toFinset.1 hx))]
  rw [hst]
  exact UniqueFactorizationMonoid.prod_normalizedFactors hf

variable (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]

theorem num_ne_zero {a : K} (ha : a ≠ 0) : IsFractionRing.num R a ≠ 0 := by
  intro h
  apply ha
  rw [← IsFractionRing.mk'_num_den' R a, h, map_zero, zero_div]

theorem den_ne_zero (a : K) : (IsFractionRing.den R a : R) ≠ 0 :=
  nonZeroDivisors.ne_zero (IsFractionRing.den R a).2

/-- **`N`-th powers up to units in the fraction field of a UFD.** -/
theorem exists_eq_unit_mul_pow {a : K} (ha : a ≠ 0) {N : ℕ}
    (h : ∀ π : R, Prime π →
      (N : ℤ) ∣ (multiplicity π (IsFractionRing.den R a : R) : ℤ) - multiplicity π (IsFractionRing.num R a)) :
    ∃ u : Rˣ, ∃ b : K, a = algebraMap R K u * b ^ N := by
  have hrel := IsFractionRing.num_den_reduced R a
  have hsplit : ∀ π : R, Prime π → N ∣ multiplicity π (IsFractionRing.num R a) ∧
      N ∣ multiplicity π (IsFractionRing.den R a : R) := by
    intro π hπ
    have h1 := h π hπ
    by_cases hn : π ∣ IsFractionRing.num R a
    · have hd : ¬ π ∣ (IsFractionRing.den R a : R) := fun hd => hπ.not_isUnit (hrel hn hd)
      rw [multiplicity_eq_zero.2 hd, Nat.cast_zero, zero_sub, Int.dvd_neg] at h1
      exact ⟨Int.natCast_dvd_natCast.1 h1, by rw [multiplicity_eq_zero.2 hd]; exact dvd_zero N⟩
    · rw [multiplicity_eq_zero.2 hn, Nat.cast_zero, sub_zero] at h1
      exact ⟨by rw [multiplicity_eq_zero.2 hn]; exact dvd_zero N, Int.natCast_dvd_natCast.1 h1⟩
  obtain ⟨d1, u1, hu1⟩ := exists_associated_pow_of_dvd_multiplicity (num_ne_zero K ha)
    (fun π hπ => (hsplit π hπ).1)
  obtain ⟨d2, u2, hu2⟩ := exists_associated_pow_of_dvd_multiplicity (den_ne_zero K a)
    (fun π hπ => (hsplit π hπ).2)
  refine ⟨u1 * u2⁻¹, algebraMap R K d1 / algebraMap R K d2, ?_⟩
  conv_lhs => rw [← IsFractionRing.mk'_num_den' R a, ← hu1, ← hu2]
  have hinv : algebraMap R K ((u2⁻¹ : Rˣ) : R) = (algebraMap R K (u2 : R))⁻¹ :=
    map_units_inv (algebraMap R K : R →* K) u2
  rw [Units.val_mul, map_mul, map_mul, map_mul, map_pow, map_pow, div_pow, hinv]
  ring

end Pow

section DVR

variable {R : Type} [CommRing R] [IsDomain R] (π : R) [(Ideal.span {π}).IsPrime]
  (D : Type) [CommRing D] [Algebra R D] [IsLocalization.AtPrime D (Ideal.span {π})]

include π in
/-- **The local ring at a prime element of a noetherian domain is a DVR** (here: a Dedekind domain). -/
theorem isDedekindDomain_atPrime [IsNoetherianRing R] : IsDedekindDomain D := by
  have : IsDomain D := IsLocalization.isDomain_of_atPrime D (Ideal.span {π})
  have : IsLocalRing D := IsLocalization.AtPrime.isLocalRing D (Ideal.span {π})
  have : IsNoetherianRing D :=
    IsLocalization.isNoetherianRing (Ideal.span {π}).primeCompl D inferInstance
  have hmax : (maximalIdeal D).IsPrincipal := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {π}) D, Ideal.map_span,
      Set.image_singleton]
    exact ⟨⟨_, rfl⟩⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := D)).out 4 2).1 hmax

variable [IsLocalRing D] [IsDedekindDomain D]

include π in
omit [IsLocalRing D] in
theorem algebraMap_atPrime_injective : Function.Injective (algebraMap R D) :=
  IsLocalization.injective D (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {π}))

theorem maximalIdeal_atPrime_eq : maximalIdeal D = Ideal.span {algebraMap R D π} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {π}) D, Ideal.map_span,
    Set.image_singleton]

/-- The closed point of `Spec R_(π)` as a height-one prime. -/
def place (hπ : π ≠ 0) : HeightOneSpectrum D where
  asIdeal := maximalIdeal D
  isPrime := (maximalIdeal.isMaximal D).isPrime
  ne_bot := by
    rw [maximalIdeal_atPrime_eq π D, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hπ (algebraMap_atPrime_injective π D (h.trans (map_zero _).symm))

/-- `log v_π(f) = -ord_π(f)` for `0 ≠ f ∈ R`. -/
theorem log_intValuation_place [WfDvdMonoid R] (hπ : π ≠ 0) {f : R} (hf : f ≠ 0) :
    WithZero.log ((place π D hπ).intValuation (algebraMap R D f)) = -(multiplicity π f : ℤ) := by
  have hprime : Prime π := (Ideal.span_singleton_prime hπ).1 inferInstance
  obtain ⟨g, hfg, hg⟩ := (FiniteMultiplicity.of_prime_left hprime hf).exists_eq_pow_mul_and_not_dvd
  have hgu : (place π D hπ).intValuation (algebraMap R D g) = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    show algebraMap R D g ∉ maximalIdeal D
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff D (Ideal.span {π}) g, Ideal.mem_span_singleton]
    exact hg
  have hπv : (place π D hπ).intValuation (algebraMap R D π) = WithZero.exp (-1 : ℤ) :=
    HeightOneSpectrum.intValuation_singleton _
      (fun h => hπ (algebraMap_atPrime_injective π D (h.trans (map_zero _).symm)))
      (maximalIdeal_atPrime_eq π D)
  conv_lhs => rw [hfg]
  rw [map_mul, map_pow, map_mul, map_pow, hgu, hπv, mul_one, WithZero.log_pow, WithZero.log_exp]
  simp

variable (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [Algebra D K] [IsScalarTower R D K]
  [IsFractionRing D K]

/-- `log v_π(a) = ord_π(den a) - ord_π(num a)` for `0 ≠ a ∈ Frac R`. -/
theorem log_valuation_place [UniqueFactorizationMonoid R] (hπ : π ≠ 0) {a : K} (ha : a ≠ 0) :
    WithZero.log ((place π D hπ).valuation K a) =
      (multiplicity π (IsFractionRing.den R a : R) : ℤ) - multiplicity π (IsFractionRing.num R a) := by
  have hn := num_ne_zero (R := R) K ha
  have hd := den_ne_zero (R := R) K a
  have hn' : algebraMap R D (IsFractionRing.num R a) ≠ 0 :=
    fun h => hn (algebraMap_atPrime_injective π D (h.trans (map_zero _).symm))
  have hd' : algebraMap R D (IsFractionRing.den R a : R) ≠ 0 :=
    fun h => hd (algebraMap_atPrime_injective π D (h.trans (map_zero _).symm))
  conv_lhs => rw [← IsFractionRing.mk'_num_den' R a]
  rw [map_div₀, IsScalarTower.algebraMap_apply R D K, IsScalarTower.algebraMap_apply R D K (IsFractionRing.den R a : R),
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    WithZero.log_div (HeightOneSpectrum.intValuation_ne_zero _ _ hn')
      (HeightOneSpectrum.intValuation_ne_zero _ _ hd'),
    log_intValuation_place π D hπ hn, log_intValuation_place π D hπ hd]
  ring

end DVR

end EtPi1
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Gal =====
section

/-!
# S4-Kummer, part 1: Kummer characters for a subgroup of a Galois group (generic field theory)

Setting: fields `K ⊆ E`, ANY subgroup `Γ ≤ Gal(E/K)` (later `π₁(U ⊗ F̄) ≤ π₁(U)`, with `E = K_U`), `N ≠ 0` and a
primitive `N`-th root of unity `ζ ∈ E` fixed by `Γ`.

* `epow ζ k = ζ ^ k` for `k : ZMod N`, `dlog` its inverse on `μ_N`;
* `rad Γ N`: the Kummer radicals, units `α` with `α ^ N` fixed by `Γ`;
* `kchar hζ α : Γ → ZMod N`, `σ α = ζ ^ (kchar α σ) α` (`kchar_spec`);
* `kchar_mul` / `kchar_mul_left`: additive in `σ` and in `α`; `kchar_eq_zero_iff`: `kchar α = 0 ↔ Γ fixes α`;
* `isLocallyConstant_kchar` (`E/K` integral, Krull topology);
* `exists_kchar_eq`: EVERY locally constant additive character `Γ → ZMod N` is a Kummer character (Hilbert 90 at a
  finite level, by Dedekind's independence of the finitely many `K`-embeddings `L₁ → E`; no normality needed);
* `kchar_conj`: equivariance, `kchar (φ α) σ = w * kchar α (φ⁻¹ σ φ)` when `φ ζ = ζ ^ w` and `φ` normalises `Γ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

noncomputable section

/-! ## Powers of `ζ` indexed by `ZMod N` and the discrete logarithm -/

section DLog

variable {E : Type} [Field E] {N : ℕ} [NeZero N] {ζ : E}

/-- `epow ζ k = ζ ^ k` for `k : ZMod N`. -/
def epow (ζ : E) (k : ZMod N) : E := ζ ^ k.val

theorem pow_mod_N (hζ : IsPrimitiveRoot ζ N) (m : ℕ) : ζ ^ (m % N) = ζ ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m N]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

@[simp] theorem epow_zero : epow ζ (0 : ZMod N) = 1 := by
  simp [epow]

theorem epow_add (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) : epow ζ (a + b) = epow ζ a * epow ζ b := by
  unfold epow
  rw [ZMod.val_add, pow_mod_N hζ, pow_add]

theorem epow_pow_N (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) : epow ζ a ^ N = 1 := by
  unfold epow
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem epow_injective (hζ : IsPrimitiveRoot ζ N) {a b : ZMod N} (h : epow ζ a = epow ζ b) : a = b :=
  ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

theorem epow_neg_mul (hζ : IsPrimitiveRoot ζ N) (a : ZMod N) : epow ζ (-a) * epow ζ a = 1 := by
  rw [← epow_add hζ, neg_add_cancel, epow_zero]

open Classical in
/-- The discrete logarithm on `μ_N` (junk value `0` off `μ_N`). -/
def dlog (hζ : IsPrimitiveRoot ζ N) (x : E) : ZMod N :=
  if h : x ^ N = 1 then ((hζ.eq_pow_of_pow_eq_one h).choose : ZMod N) else 0

theorem epow_dlog (hζ : IsPrimitiveRoot ζ N) {x : E} (h : x ^ N = 1) : epow ζ (dlog hζ x) = x := by
  have hs := (hζ.eq_pow_of_pow_eq_one h).choose_spec
  unfold dlog epow
  rw [dif_pos h, ZMod.val_natCast, Nat.mod_eq_of_lt hs.1, hs.2]

theorem dlog_epow (hζ : IsPrimitiveRoot ζ N) (k : ZMod N) : dlog hζ (epow ζ k) = k :=
  epow_injective hζ (epow_dlog hζ (epow_pow_N hζ k))

end DLog

/-! ## Kummer radicals and Kummer characters -/

section Radicals

variable {K E : Type} [Field K] [Field E] [Algebra K E] (Γ : Subgroup (E ≃ₐ[K] E)) (N : ℕ)

/-- Kummer radicals: units `α` whose `N`-th power is fixed by `Γ`. -/
def rad : Subgroup Eˣ where
  carrier := {α | ∀ σ ∈ Γ, σ ((α : E) ^ N) = (α : E) ^ N}
  mul_mem' := by
    intro a b ha hb σ hσ
    simp only [Units.val_mul, mul_pow, map_mul, ha σ hσ, hb σ hσ]
  one_mem' := by
    intro σ _
    simp
  inv_mem' := by
    intro a ha σ hσ
    simp only [Units.val_inv_eq_inv_val, inv_pow, map_inv₀, ha σ hσ]

theorem mem_rad (α : Eˣ) : α ∈ rad Γ N ↔ ∀ σ ∈ Γ, σ ((α : E) ^ N) = (α : E) ^ N := Iff.rfl

/-- Units fixed by `Γ` (the multiplicative group of the fixed field). -/
def fixUnits : Subgroup Eˣ where
  carrier := {α | ∀ σ ∈ Γ, σ (α : E) = α}
  mul_mem' := by
    intro a b ha hb σ hσ
    simp only [Units.val_mul, map_mul, ha σ hσ, hb σ hσ]
  one_mem' := by
    intro σ _
    simp
  inv_mem' := by
    intro a ha σ hσ
    simp only [Units.val_inv_eq_inv_val, map_inv₀, ha σ hσ]

theorem mem_fixUnits (α : Eˣ) : α ∈ fixUnits Γ ↔ ∀ σ ∈ Γ, σ (α : E) = α := Iff.rfl

variable {Γ N}

theorem ratio_pow {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) :
    ((σ : E ≃ₐ[K] E) (α : E) / α) ^ N = 1 := by
  rw [div_pow, ← map_pow, hα σ σ.2, div_self (pow_ne_zero _ α.ne_zero)]

variable [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)

/-- The Kummer character of `α`: `σ α = ζ ^ (kchar α σ) α`. -/
def kchar (α : Eˣ) (σ : Γ) : ZMod N := dlog hζ ((σ : E ≃ₐ[K] E) (α : E) / α)

theorem kchar_spec {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) :
    (σ : E ≃ₐ[K] E) (α : E) = epow ζ (kchar hζ α σ) * α := by
  rw [kchar, epow_dlog hζ (ratio_pow hα σ), div_mul_cancel₀ _ α.ne_zero]

theorem kchar_eq_iff {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) (k : ZMod N) :
    kchar hζ α σ = k ↔ (σ : E ≃ₐ[K] E) (α : E) = epow ζ k * α := by
  constructor
  · rintro rfl
    exact kchar_spec hζ hα σ
  · intro h
    rw [kchar, h, mul_div_cancel_right₀ _ α.ne_zero, dlog_epow]

theorem map_epow {σ : E ≃ₐ[K] E} (hσ : σ ζ = ζ) (k : ZMod N) : σ (epow ζ k) = epow ζ k := by
  unfold epow
  rw [map_pow, hσ]

variable (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)
include hζΓ

end Radicals

section Radicals2

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)} {N : ℕ} [NeZero N]
  {ζ : E} (hζ : IsPrimitiveRoot ζ N)

theorem kchar_eq_zero_iff {α : Eˣ} (hα : α ∈ rad Γ N) :
    (∀ σ : Γ, kchar hζ α σ = 0) ↔ α ∈ fixUnits Γ := by
  constructor
  · intro h σ hσ
    have := (kchar_eq_iff hζ hα ⟨σ, hσ⟩ 0).1 (h ⟨σ, hσ⟩)
    rw [epow_zero, one_mul] at this
    exact this
  · intro h σ
    rw [kchar_eq_iff hζ hα, epow_zero, one_mul]
    exact h σ σ.2

/-! ## Surjectivity: every locally constant character is a Kummer character (Hilbert 90) -/

/-- Every locally constant additive character `c : Γ → ZMod N` is `kchar α` for a radical `α`. -/
theorem exists_kchar_eq (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ) (c : Γ → ZMod N) (hc : IsLocallyConstant c)
    (hhom : ∀ σ τ : Γ, c (σ * τ) = c σ + c τ) : ∃ α ∈ rad Γ N, ∀ σ : Γ, kchar hζ α σ = c σ := by
  classical
  have hc1 : c 1 = 0 := by
    have h := hhom 1 1
    rw [mul_one] at h
    linear_combination -h
  have hcinv : ∀ σ : Γ, c σ⁻¹ = - c σ := by
    intro σ
    have h := hhom σ⁻¹ σ
    rw [inv_mul_cancel, hc1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  -- a finite level `L₁` with `Fix(L₁) ∩ Γ ⊆ ker c`
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp (hc.isOpen_fiber (0 : ZMod N))
  have h1t : (1 : E ≃ₐ[K] E) ∈ t := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' t := by
      rw [hts]
      exact hc1
    exact this
  obtain ⟨L₁, hfin, hL₁⟩ := (krullTopology_mem_nhds_one_iff K E t).mp (ht.mem_nhds h1t)
  have hker : ∀ σ : Γ, (σ : E ≃ₐ[K] E) ∈ L₁.fixingSubgroup → c σ = 0 := by
    intro σ hσ
    have : σ ∈ Subtype.val ⁻¹' t := hL₁ hσ
    rw [hts] at this
    exact this
  -- restriction to `L₁`
  let res : Γ → (L₁ →ₐ[K] E) := fun σ => ((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp L₁.val
  have hres : ∀ σ τ : Γ, res σ = res τ → c σ = c τ := by
    intro σ τ h
    have hfix : ((σ⁻¹ * τ : Γ) : E ≃ₐ[K] E) ∈ L₁.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' : (σ : E ≃ₐ[K] E) x = (τ : E ≃ₐ[K] E) x := DFunLike.congr_fun h ⟨x, hx⟩
      show (σ : E ≃ₐ[K] E)⁻¹ ((τ : E ≃ₐ[K] E) x) = x
      rw [← hx', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have h0 := hker _ hfix
    have h2 := hhom σ (σ⁻¹ * τ)
    rw [mul_inv_cancel_left, h0, add_zero] at h2
    exact h2.symm
  -- the coefficients
  let f : (L₁ →ₐ[K] E) → E := fun h => if hh : ∃ σ : Γ, res σ = h then epow ζ (-c hh.choose) else 0
  have f_res : ∀ σ : Γ, f (res σ) = epow ζ (-c σ) := by
    intro σ
    have hh : ∃ τ : Γ, res τ = res σ := ⟨σ, rfl⟩
    simp only [f, dif_pos hh]
    rw [hres _ _ hh.choose_spec]
  have hcomp : ∀ (σ τ : Γ), (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp (res τ)) = res (σ * τ) := by
    intro σ τ
    ext x
    rfl
  have f_comp : ∀ (σ : Γ) (h : L₁ →ₐ[K] E),
      f ((((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)) = epow ζ (-c σ) * f h := by
    intro σ h
    by_cases hh : ∃ τ : Γ, res τ = h
    · obtain ⟨τ, rfl⟩ := hh
      rw [hcomp, f_res, f_res, hhom, neg_add, epow_add hζ]
    · have hh' : ¬ ∃ τ : Γ, res τ = (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h) := by
        rintro ⟨τ, hτ⟩
        apply hh
        refine ⟨σ⁻¹ * τ, ?_⟩
        rw [← hcomp, hτ]
        ext x
        show (σ : E ≃ₐ[K] E)⁻¹ ((σ : E ≃ₐ[K] E) (h x)) = h x
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      simp only [f, dif_neg hh, dif_neg hh', mul_zero]
  -- Dedekind independence of the finitely many embeddings `L₁ → E`
  have : Finite (L₁ →ₐ[K] E) := Finite.algHom K L₁ E
  let _ : Fintype (L₁ →ₐ[K] E) := Fintype.ofFinite _
  have hLI : LinearIndependent E (fun h : L₁ →ₐ[K] E => (h : L₁ → E)) := by
    have := (linearIndependent_monoidHom L₁ E).comp (fun h : L₁ →ₐ[K] E => (h : L₁ →* E))
      (fun a b hab => AlgHom.ext fun x => DFunLike.congr_fun hab x)
    exact this
  have hsum : ∃ z : L₁, ∑ h, f h * h z ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    have hz : ∑ h, f h • (h : L₁ → E) = 0 := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hcon z
    have := (Fintype.linearIndependent_iff.mp hLI) f hz (res 1)
    rw [f_res, hc1, neg_zero, epow_zero] at this
    exact one_ne_zero this
  obtain ⟨z, hz⟩ := hsum
  set β := ∑ h, f h * h z with hβdef
  have hfσ : ∀ (σ : Γ) (h : L₁ →ₐ[K] E), (σ : E ≃ₐ[K] E) (f h) = f h := by
    intro σ h
    by_cases hh : ∃ τ : Γ, res τ = h
    · simp only [f, dif_pos hh]
      exact map_epow (hζΓ σ σ.2) _
    · simp only [f, dif_neg hh, map_zero]
  have hσβ : ∀ σ : Γ, (σ : E ≃ₐ[K] E) β = epow ζ (c σ) * β := by
    intro σ
    let e : (L₁ →ₐ[K] E) ≃ (L₁ →ₐ[K] E) :=
      { toFun := fun h => (((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)
        invFun := fun h => ((((σ : E ≃ₐ[K] E)⁻¹ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h)
        left_inv := fun h => by
          ext x
          show (σ : E ≃ₐ[K] E)⁻¹ ((σ : E ≃ₐ[K] E) (h x)) = h x
          rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
        right_inv := fun h => by
          ext x
          show (σ : E ≃ₐ[K] E) ((σ : E ≃ₐ[K] E)⁻¹ (h x)) = h x
          rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] }
    have step1 : (σ : E ≃ₐ[K] E) β = ∑ h, f h * (e h) z := by
      rw [hβdef, map_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, hfσ]
      rfl
    have step2 : ∀ h, f h = epow ζ (c σ) * f (e h) := by
      intro h
      show f h = epow ζ (c σ) * f ((((σ : E ≃ₐ[K] E) : E →ₐ[K] E).comp h))
      rw [f_comp, ← mul_assoc, mul_comm (epow ζ (c σ)), epow_neg_mul hζ, one_mul]
    rw [step1]
    have step3 : ∑ h, f h * (e h) z = ∑ h, epow ζ (c σ) * (f (e h) * (e h) z) :=
      Finset.sum_congr rfl fun h _ => by rw [← mul_assoc, ← step2 h]
    rw [step3, ← Finset.mul_sum, Equiv.sum_comp e (fun h => f h * h z)]
  refine ⟨Units.mk0 β hz, ?_, ?_⟩
  · intro σ hσ
    rw [Units.val_mk0, map_pow, hσβ ⟨σ, hσ⟩, mul_pow, epow_pow_N hζ, one_mul]
  · intro σ
    rw [kchar_eq_iff hζ (by
      intro σ hσ
      rw [Units.val_mk0, map_pow, hσβ ⟨σ, hσ⟩, mul_pow, epow_pow_N hζ, one_mul]), Units.val_mk0]
    exact hσβ σ

end Radicals2

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtSheaves_Trans =====
section

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

end

end

-- ===== S4.Def_RP_EtSheaves_ConstFix =====
section

/-!
# S4-EtSheaves, O10c part 3: Galois elements fixing a trivialising lift act trivially

Let `g : Y ⟶ X` be etale with `g^* F ≅ M_Y` constant, and `t` a geometric point of `Y`. Every element of
`F_(t ≫ g)` is the germ of a section of `F` over `Y → X` at the lift `t` (`exists_germ_of_triv`). Hence an
automorphism `τ` of `Spec Ω` with `τ ≫ t = t` acts trivially on `F_(t ≫ g)` (`stalkAut_triv_eq_id`), and
`σ ∈ Gal(κ(x)^sep/κ(x))` with `Spec σ ≫ l = l` for a lift `l : Spec Ω ⟶ Y` of `x̄` acts trivially on `F_x̄`
(`galRep_eq_id_of_triv`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ]

/-- The stalk of `φ : M_Y ⟶ G` on the constant germ of `m` is the germ of `φ(m)` over the identity. -/
theorem stalkMap_constGerm {Y : Scheme.{u}} {M : ModuleCat.{u} Λ} {G : EtSh Λ Y} (φ : constSh Λ Y M ⟶ G)
    (t : GeomPt Y) (m : M) :
    ((t.stalkF Λ).map φ).hom ((constStalkIso Λ t M).inv.hom m) =
      (t.point.toPresheafFiber (etId Y) t.top G.obj).hom
        ((φ.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom m)) := by
  rw [← constUnit_germ t M (etId Y) t.top]
  change (constUnit M (etId Y) ≫ t.point.toPresheafFiber (etId Y) t.top (constSh Λ Y M).obj ≫
    t.point.presheafFiber.map φ.hom).hom m = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g]

/-- If `g^* F` is constant, every element of `F_(t ≫ g)` is a germ at the lift `t` over `Y → X`. -/
theorem exists_germ_of_triv (F : EtSh Λ X) (M : ModuleCat.{u} Λ) (e : (pull g Λ).obj F ≅ constSh Λ Y M)
    (t : GeomPt Y) (v : ((t.map g).stalkF Λ).obj F) :
    ∃ z : F.obj.obj (op ((etComp g).obj (etId Y))),
      ((t.map g).point.toPresheafFiber ((etComp g).obj (etId Y)) (liftX g t t.top) F.obj).hom z = v := by
  let e' : constSh Λ Y M ≅ (res g Λ).obj F := e.symm ≪≫ (pullIsoRes g Λ).app F
  let E : (t.stalkF Λ).obj ((res g Λ).obj F) ≅ M := (t.stalkF Λ).mapIso e'.symm ≪≫ constStalkIso Λ t M
  let w := (resFibIso g t Λ F).inv.hom v
  refine ⟨(e'.hom.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom (E.hom.hom w)), ?_⟩
  have hw : ((t.stalkF Λ).map e'.hom).hom ((constStalkIso Λ t M).inv.hom (E.hom.hom w)) = w := by
    change (E.hom ≫ E.inv).hom w = w
    rw [E.hom_inv_id]
    rfl
  have h1 := stalkMap_constGerm e'.hom t (E.hom.hom w)
  have h2 := resFib_germ g t Λ F (etId Y) t.top
    ((e'.hom.hom.app (op (etId Y))).hom ((constUnit M (etId Y)).hom (E.hom.hom w)))
  have h3 : (resFib g t Λ F).hom w = v := by
    change ((resFibIso g t Λ F).inv ≫ (resFibIso g t Λ F).hom).hom v = v
    rw [Iso.inv_hom_id]
    rfl
  exact h2.symm.trans ((congrArg (resFib g t Λ F).hom (h1.symm.trans hw)).trans h3)

/-- An automorphism `τ` of `Spec Ω` fixing the geometric point `t` of a trivialising `Y` acts trivially on
`F_(t ≫ g)`. -/
theorem stalkAut_triv_eq_id (F : EtSh Λ X) (M : ModuleCat.{u} Λ) (e : (pull g Λ).obj F ≅ constSh Λ Y M)
    (t : GeomPt Y) (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω))
    (hτ : τ ≫ (t.map g).pt = (t.map g).pt) (hfix : τ ≫ t.pt = t.pt) :
    (((t.map g).stalkAut Λ τ hτ).app F).hom = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨z, rfl⟩ := exists_germ_of_triv g F M e t v
  exact GeomPt.stalkAut_fix (t.map g) Λ τ hτ F _ (liftX g t t.top) z hfix

/-- The same for any geometric point `s` of `X` with a lift `l : Spec Ω ⟶ Y` fixed by `τ`. -/
theorem stalkAut_eq_id_of_lift (F : EtSh Λ X) (M : ModuleCat.{u} Λ) (e : (pull g Λ).obj F ≅ constSh Λ Y M)
    (s : GeomPt X) (l : Spec (CommRingCat.of s.Ω) ⟶ Y) (hl : l ≫ g = s.pt)
    (τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)) (hτ : τ ≫ s.pt = s.pt)
    (hfix : τ ≫ l = l) :
    ((s.stalkAut Λ τ hτ).app F).hom = LinearMap.id := by
  obtain ⟨Ω, pt⟩ := s
  change Spec (CommRingCat.of Ω) ⟶ Y at l
  change Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of Ω) at τ
  revert pt
  intro pt hl hτ hfix
  change l ≫ g = pt at hl
  subst hl
  exact stalkAut_triv_eq_id g F M e ⟨Ω, l⟩ τ hτ hfix

/-- **HEADLINE (O10c, F3)**: if `g^* F` is constant and `σ ∈ Gal(κ(x)^sep/κ(x))` fixes a lift
`l : Spec κ(x)^sep ⟶ Y` of the geometric point `x̄`, then `σ` acts trivially on `F_x̄`. -/
theorem galRep_eq_id_of_triv (F : EtSh Λ X) (x : X) (M : ModuleCat.{u} Λ)
    (e : (pull g Λ).obj F ≅ constSh Λ Y M)
    (l : Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ Y) (hl : l ≫ g = (geomPtAt x).pt)
    (σ : Gal x) (hσ : galSpec x σ ≫ l = l) :
    galRep Λ F x σ = LinearMap.id :=
  stalkAut_eq_id_of_lift g F M e (geomPtAt x) l hl (galSpec x σ) (galSpec_comp x σ) hσ

/-- **HEADLINE (O10c, F3), etale-neighbourhood form**: the same for `U : X.Etale` with `F|_U ≅ M_U`. -/
theorem galRep_eq_id_of_etale (F : EtSh Λ X) (x : X) (U : X.Etale) (M : ModuleCat.{u} Λ)
    (e : (pull U.hom Λ).obj F ≅ constSh Λ U.left M)
    (l : Spec (CommRingCat.of (SeparableClosure (X.residueField x))) ⟶ U.left)
    (hl : l ≫ U.hom = (geomPtAt x).pt) (σ : Gal x) (hσ : galSpec x σ ≫ l = l) :
    galRep Λ F x σ = LinearMap.id := by
  have : Etale U.hom := U.prop
  exact galRep_eq_id_of_triv U.hom F x M e l hl σ hσ

end RamanujanPetersson.EtSheaves

end

end


