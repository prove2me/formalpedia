-- Prove2me | Definitions.Def_WeierstrassCurve_ProjModel
-- name    : WeierstrassCurve_ProjModel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/f7df0dd6-b343-56da-8e1a-41dd5eedce2a
-- title:
--   Proj model of a Weierstrass curve; relative group laws
-- statement:
--   For a commutative ring $R$ and $V : \mathtt{WeierstrassCurve.Projective}\ R$, the homogeneous cubic $V.\mathtt{polynomial}$ in $R[X_0,X_1,X_2]$ generates an ideal that is homogeneous for the standard grading (`span_polynomial_isHomogeneousCR`, from homogeneity of degree $3$); `projModelHomogeneousIdealCR` packages it as a homogeneous ideal, `ProjModelRingCR` is the quotient $\mathrm{MvPolynomial}(\mathrm{Fin}\ 3, R)/(V.\mathtt{polynomial})$, `projModelGradingCR` is the induced grading by images of the homogeneous pieces, `projModelCR` is its `Proj`, and `projModelStrCR` is the structure morphism to $\operatorname{Spec} R$, namely `Proj.toSpecZero` followed by the map induced by $R \to (\text{degree-}0\text{ part})$.
--
--   Group laws are recorded in functor-of-points form. For a test scheme $t : T \to \operatorname{Spec} R$, relative points are the morphisms to $A$ over $\operatorname{Spec} R$, and `schemeHomOverComp` is the transition map along $\psi : T' \to T$ with $\psi \circ t = t'$ (composition with $\psi$). A `RelativeGroupLaw R f`, for $f : A \to \operatorname{Spec} R$, is data: a multiplication, unit and inverse on every relative point set, with associativity, both unit laws, the left inverse law, and naturality of multiplication in the test scheme. Naturality of the unit and of the iterated powers `nsmul` is derived; `pointGroup` exhibits each point set as a group; `IsTorsionPoint t n x` says the $n$-th power of $x$ is the unit, `torsionSubset` the set of these, stable under transition maps. On the scheme level, `schemeNsmul n` is the endomorphism of $A$ underlying the $n$-th power of the identity point, `schemeKer n` is its pullback against the unit section over $\operatorname{Spec} R$, with structure morphism `schemeKerStr`.
--
--   Finally `galTwist` twists an $F$-point by $\sigma \in \mathrm{Aut}_R(F)$ by precomposing with $\operatorname{Spec} \sigma$, and `IsPointsEval V G ev` is the predicate on a given family of bijections $ev$ from $F$-points of the Proj model to $(V_{/F})$-affine points asserting that $ev$ carries the relative multiplication to addition of affine points and intertwines `galTwist` with `Point.map`. Separately, `ext_of_isSchemeTheoreticallyDominant_of_isSeparated` states that two morphisms $f, g : X \to Y$ are equal as soon as they agree after composing with a separated $s : Y \to Z$ and after precomposing with a scheme-theoretically dominant $\iota : W \to X$.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve.Projective` with its homogeneous cubic, the affine point group, and `Proj` of a graded algebra; the Proj model of the Weierstrass cubic, the relative (functor-of-points) group-law structure with its power maps and kernel schemes, and the points-evaluation predicate are the project's own, as is the extension-of-morphisms lemma for dominant source and separated target.
--
--   **Where it is used.** This vocabulary supports the study of finite flat models of the torsion of the Frey curve at primes of good reduction, where the group of field-valued points of a Weierstrass curve must be compared, Galois-equivariantly, with the relative points of an integral model and with kernels of multiplication by $n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ProjModel.lean

import Definitions.Def_AlgebraicGeometry_HomogeneousIdealQuotientGradingInfra
import Definitions.Def_AlgebraicGeometry_ProjectiveWeierstrassPolynomialPrime
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Pullbacks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeierstrassProjModel

theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W X Y Z : Scheme.{u}}
    {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›

  have hcond : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU

  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    have h1 : (equalizer.ι f' g').left.ker ≤
        ((equalizer.lift ι' hcond ≫ equalizer.ι f' g').left).ker := by
      rw [Over.comp_left]
      exact Scheme.Hom.le_ker_comp _ _
    rw [equalizer.lift_ι] at h1
    have h2 : (ι'.left).ker = ⊥ := Scheme.Hom.ker_eq_bot ι
    exact le_bot_iff.mp (h1.trans (le_of_eq h2))

  haveI : IsClosedImmersion (equalizer.ι f' g').left := inferInstance
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact (cancel_epi (equalizer.ι f' g').left).mp congr($(equalizer.condition f' g').left)

end WeierstrassProjModel

namespace WeierstrassProjModel

open NeronModelInfra

def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩

@[simp]
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl

structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) where

  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f

  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f

  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f

  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)

  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t (one t) x = x

  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t x (one t) = x

  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f), mul t (inv t x) x = one t

  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n

@[simp]
theorem nsmul_zero (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 0 x = G.one t :=
  rfl

@[simp]
theorem nsmul_succ (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (n + 1) x = G.mul t (G.nsmul t n x) x :=
  rfl

theorem nsmul_one_apply (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 1 x = x := by
  show G.mul t (G.one t) x = x
  exact G.one_mul t x

theorem nsmul_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.nsmul t n (G.one t) = G.one t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, ih, G.mul_one]

@[reducible]
def pointGroup (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : Group (SchemeHomOver t f) where
  mul x y := G.mul t x y
  one := G.one t
  inv x := G.inv t x
  mul_assoc := G.mul_assoc t
  one_mul := G.one_mul t
  mul_one := G.mul_one t
  inv_mul_cancel := G.inv_mul_cancel t

theorem one_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (G.one t) = G.one t' := by
  have h : G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t)) =
      schemeHomOverComp ψ hψ (G.one t) := by
    rw [← G.mul_natural t t' ψ hψ, G.one_mul]
  calc schemeHomOverComp ψ hψ (G.one t)
      = G.mul t' (G.one t') (schemeHomOverComp ψ hψ (G.one t)) := (G.one_mul t' _).symm
    _ = G.mul t' (G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t))) (schemeHomOverComp ψ hψ (G.one t)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t))) := by
        rw [G.mul_assoc]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t)) := by rw [h]
    _ = G.one t' := G.inv_mul_cancel t' _

theorem nsmul_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.nsmul t n x) = G.nsmul t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero =>
      show schemeHomOverComp ψ hψ (G.one t) = G.one t'
      exact G.one_natural t t' ψ hψ
  | succ n ih =>
      calc schemeHomOverComp ψ hψ (G.nsmul t (n + 1) x)
          = schemeHomOverComp ψ hψ (G.mul t (G.nsmul t n x) x) := rfl
        _ = G.mul t' (schemeHomOverComp ψ hψ (G.nsmul t n x)) (schemeHomOverComp ψ hψ x) :=
            G.mul_natural t t' ψ hψ _ _
        _ = G.mul t' (G.nsmul t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x) := by
            rw [ih]
        _ = G.nsmul t' (n + 1) (schemeHomOverComp ψ hψ x) := rfl

def IsTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : Prop :=
  G.nsmul t n x = G.one t

theorem isTorsionPoint_def (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t n x ↔ G.nsmul t n x = G.one t :=
  Iff.rfl

def torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) : Set (SchemeHomOver t f) :=
  {x | G.IsTorsionPoint t n x}

@[simp]
theorem mem_torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x ∈ G.torsionSubset t n ↔ G.IsTorsionPoint t n x :=
  Iff.rfl

theorem isTorsionPoint_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.IsTorsionPoint t n (G.one t) :=
  G.nsmul_unit t n

theorem isTorsionPoint_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t 1 x ↔ x = G.one t := by
  show G.nsmul t 1 x = G.one t ↔ x = G.one t
  rw [G.nsmul_one_apply]

theorem isTorsionPoint_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) {x : SchemeHomOver t f}
    (hx : G.IsTorsionPoint t n x) :
    G.IsTorsionPoint t' n (schemeHomOverComp ψ hψ x) := by
  show G.nsmul t' n (schemeHomOverComp ψ hψ x) = G.one t'
  rw [← G.nsmul_natural t t' ψ hψ n x, hx]
  exact G.one_natural t t' ψ hψ

theorem mapsTo_torsionSubset_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) :
    Set.MapsTo (schemeHomOverComp ψ hψ) (G.torsionSubset t n) (G.torsionSubset t' n) :=
  fun _ hx => G.isTorsionPoint_schemeHomOverComp t t' ψ hψ n hx

end RelativeGroupLaw

end WeierstrassProjModel
end

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace WeierstrassProjModel

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev idPoint : SchemeHomOver f f :=
  ⟨𝟙 A, Category.id_comp f⟩

def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).1

theorem schemeNsmul_over (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeNsmul n ≫ f = f :=
  (G.nsmul f n idPoint).2

abbrev schemeKer (G : RelativeGroupLaw R f) (n : ℕ) : Scheme.{u} :=
  pullback (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev schemeKerStr (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeKer n ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

end RelativeGroupLaw

end WeierstrassProjModel

end

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime
open NeronModelInfra

namespace WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

section Carrier

variable {R : Type*} [CommRing R]

theorem span_polynomial_isHomogeneousCR (V : WeierstrassCurve.Projective R) :
    (Ideal.span {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact ⟨3, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_polynomial V)⟩

def projModelHomogeneousIdealCR (V : WeierstrassCurve.Projective R) :
    HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) :=
  ⟨Ideal.span {V.polynomial}, span_polynomial_isHomogeneousCR V⟩

@[simp]
theorem projModelHomogeneousIdealCR_toIdeal (V : WeierstrassCurve.Projective R) :
    (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial} := rfl

abbrev ProjModelRingCR (V : WeierstrassCurve.Projective R) : Type _ :=
  MvPolynomial (Fin 3) R ⧸ (projModelHomogeneousIdealCR V).toIdeal

abbrev projModelGradingCR (V : WeierstrassCurve.Projective R) :
    ℕ → Submodule R (ProjModelRingCR V) :=
  quotGradingSubmodule (homogeneousSubmodule (Fin 3) R) (projModelHomogeneousIdealCR V).toIdeal

abbrev projModelCR (V : WeierstrassCurve.Projective R) : Scheme :=
  Proj (projModelGradingCR V)

def projModelStrCR (V : WeierstrassCurve.Projective R) :
    Proj (projModelGradingCR V) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (projModelGradingCR V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))

end Carrier

section PointsEval

variable {R : Type u} [CommRing R]

def galTwist {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {F : Type u} [Field F]
    [Algebra R F] (σ : F ≃ₐ[R] F)
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) f) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) f :=
  schemeHomOverComp (Spec.map (CommRingCat.ofHom (σ : F →+* F)))
    (by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom
        (RingHom.ext fun x => σ.commutes x)))
    P

def IsPointsEval (V : WeierstrassCurve.Projective R)
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point) : Prop :=
  (∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F]
      (P Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F)))
        (projModelStrCR V)),
      ev F (G.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) P Q) = ev F P + ev F Q) ∧
  (∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F] (σ : F ≃ₐ[R] F)
      (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F)))
        (projModelStrCR V)),
      ev F (galTwist σ P) =
        WeierstrassCurve.Affine.Point.map (σ : F →ₐ[R] F) (ev F P))

end PointsEval

end WeierstrassProjModel

end


