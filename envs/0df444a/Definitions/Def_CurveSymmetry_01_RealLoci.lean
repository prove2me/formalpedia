-- Prove2me | Definitions.Def_CurveSymmetry_01_RealLoci
-- name    : CurveSymmetry_01_RealLoci
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:09:25.154879+00:00
-- url     : https://prove2.me/theorems/15a47b4d-ddff-40cd-8a89-28d343217681
-- title:
--   Real loci in the coordinates $z,\bar z$, Euclidean symmetry parameters, and the strict transform $H_{m,\alpha}$
-- statement:
--   Let $\mathbb C[X,Y]$ be the ring of complex polynomials in two variables. As in the note, a point $z\in\mathbb C$ of the plane is given the coordinates $(X,Y)=(z,\bar z)$, so that $P\in\mathbb C[X,Y]$ is read on the plane through $z\mapsto P(z,\bar z)$; monomials $X^aY^b$ are indexed by exponent pairs $(a,b)\in\mathbb N^2$. We also use the rings $\mathbb C[t]$ and $\mathbb C[t][Y]$ (polynomials in $Y$ with coefficients in $\mathbb C[t]$), an integer $m\in\mathbb N$, and complex parameters $\alpha,\zeta,a,b,c,v,z$.
--
--   The basic object is the real locus of $P$ in complex coordinates,
--   $$Z(P)=\{z\in\mathbb C : P(z,\bar z)=0\}.$$
--   Around it the file defines:
--
--   1. Substitution endomorphisms of $\mathbb C[X,Y]$: the rotation pullback $P(X,Y)\mapsto P(\zeta X,\zeta^{-1}Y)$; the translation pullback $P(X,Y)\mapsto P(X+c,\,Y+\bar c)$ along $z\mapsto z+c$; the reflection pullback $P(X,Y)\mapsto P(aY,\,\bar aX)$ along $z\mapsto a\bar z$; and the conjugate swap $P\mapsto\overline P(Y,X)$, where $\overline P$ has the conjugate coefficients.
--   2. The group of rotations about the origin preserving $Z(P)$: the subgroup of $\mathbb C^\times$ formed by the $u$ with $|u|=1$ and $uz\in Z(P)\iff z\in Z(P)$ for every $z\in\mathbb C$, together with its inclusion into the multiplicative monoid of $\mathbb C$.
--   3. Euclidean symmetries in complex affine form. For $S\subseteq\mathbb C$, a pair $(a,b)\in\mathbb C^2$ is a direct symmetry of $S$ if $|a|=1$ and $az+b\in S\iff z\in S$ for all $z$, and an opposite symmetry of $S$ if $|a|=1$ and $a\bar z+b\in S\iff z\in S$ for all $z$. For $P$ the file forms the set of direct symmetry pairs of $Z(P)$, the set of opposite ones, and their disjoint union.
--   4. The condition that $Z(P)$ is not a circle: $Z(P)\ne\{z : |z-c|=R\}$ for every $c\in\mathbb C$ and every real $R>0$.
--   5. Lines: the restriction homomorphism $\mathbb C[X,Y]\to\mathbb C[s]$, $X\mapsto z+vs$, $Y\mapsto\bar z+\bar vs$, and the line polynomial $\bar vX-vY-(\bar vz-v\bar z)$, which vanishes at $(w,\bar w)$ for every $w=z+sv$ with $s\in\mathbb R$.
--   6. Nested coordinates: the $\mathbb C$-algebra isomorphism $\mathbb C[X,Y]\cong\mathbb C[Y][X]$ making $X$ the outer variable, and the evaluation of nested polynomials at a point $(x,y)\in\mathbb C^2$.
--
--   Finally, for the chart $X=tY$ of equation (7), it defines
--   $$A_{m,\alpha}(t)=\alpha t^m+\bar\alpha,\qquad B_m(t)=t(t^m+1),\qquad H_{m,\alpha}=A_{m,\alpha}(t)+B_m(t)\,Y^2\in\mathbb C[t][Y],$$
--   together with the reversed quadratic $B_m(t)+A_{m,\alpha}(t)\,Y^2$.
--
--   These objects are the vocabulary in which the degree bounds are formalized. The curve $C$ of Theorem 1 is $Z(P)$ for its complexification $P$, and the non-circle condition is the hypothesis that $C$ is not a circle; the rotation pullback is the substitution in the weight criterion (4); the rotation group about the origin and the sets of symmetry pairs parametrize the symmetries studied in Lemma 3 and counted in Theorem 1; the line restriction and the line polynomial serve the exclusion of translations in the proof of Lemma 3. The polynomials $A_{m,\alpha}$, $B_m$ and $H_{m,\alpha}$ are those of equation (7), the double-cover chart used in the proof of Lemma 4.
--
--   **Formalization Note**: Polynomials in two variables are `MvPolynomial (Fin 2) ℂ`, with $X$ and $Y$ the variables indexed $0$ and $1$. The rotation pullback is defined for every $\zeta\in\mathbb C$, with Lean's convention $0^{-1}=0$. Symmetries are recorded by their parameters $(a,b)$; their comparison with actual isometries of $\mathbb C$ is a separate statement. Besides definitions, the file keeps with proofs the facts later parts need, notably that $H_{m,\alpha}$ and its reversal are irreducible in $\mathbb C[t][Y]$ whenever $m\ge1$ and $\alpha\ne\bar\alpha$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules RotationSupport, Irreducibility, RealLocus, Elimination, GeometricRotation, RotationGroup, Translation, EuclideanCenter, ChangeCenter, DirectBound, Reflection, EuclideanParameters, FamilyQuadratic in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 01 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

-- lean/RotationSupport.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

abbrev BPoly := MvPolynomial (Fin 2) ℂ

abbrev Exponent := Fin 2 →₀ ℕ

noncomputable def rotate (ζ : ℂ) : BPoly →+* BPoly :=
  eval₂Hom C (fun i => C (if i = 0 then ζ else ζ⁻¹) * X i)

lemma exponent_decompose (s : Exponent) :
    s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) := by
  ext i
  fin_cases i <;> simp

lemma exponent_degree (s : Exponent) : s.sum (fun _ e => e) = s 0 + s 1 := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two]

lemma support_degree {P : BPoly} {s : Exponent} (hs : s ∈ P.support) :
    s 0 + s 1 ≤ P.totalDegree := by
  simpa [exponent_degree] using le_totalDegree hs

noncomputable def exponent (a b : ℕ) : Exponent :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma exponent_zero (a b : ℕ) : exponent a b 0 = a := by simp [exponent]

@[simp] lemma exponent_one (a b : ℕ) : exponent a b 1 = b := by simp [exponent]

lemma exponent_eq_iff {s : Exponent} {a b : ℕ} :
    s = exponent a b ↔ s 0 = a ∧ s 1 = b := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1⟩
    rw [exponent_decompose s, h0, h1]
    rfl

lemma monomial_exponent (a b : ℕ) (c : ℂ) :
    monomial (exponent a b) c = C c * (X 0 : BPoly) ^ a * X 1 ^ b := by
  simp [X_pow_eq_monomial, C_mul_monomial, monomial_mul, exponent]

end CurveSymmetry

end

-- lean/Irreducibility.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

lemma linear_degree_le (c : ℂ) : ((X 0 : BPoly) - C c * X 1).totalDegree ≤ 1 := by
  have hmul := totalDegree_mul (C c : BPoly) (X 1)
  have hsub := totalDegree_sub (X 0 : BPoly) (C c * X 1)
  simp only [totalDegree_C, totalDegree_X, zero_add] at hmul hsub
  omega

end CurveSymmetry

end

-- lean/RealLocus.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- The real locus in complex coordinates: `X=z`, `Y=conj z`. -/
def realLocus (P : BPoly) : Set ℂ :=
  {z | eval (fun i : Fin 2 => if i = 0 then z else star z) P = 0}

end CurveSymmetry

end

-- lean/Elimination.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

abbrev UPoly := Polynomial ℂ

abbrev NPoly := Polynomial UPoly

noncomputable def toNested : BPoly ≃ₐ[ℂ] NPoly :=
  (finSuccEquiv ℂ 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv ℂ (Fin 1)))

noncomputable def nestedEval (x y : ℂ) : NPoly →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom y) x

lemma toNested_C (c : ℂ) : toNested (C c) = Polynomial.C (Polynomial.C c) := by
  simp [toNested, finSuccEquiv_apply, uniqueAlgEquiv]

lemma toNested_X_zero : toNested (X 0) = Polynomial.X := by
  simp [toNested, finSuccEquiv_X_zero]

lemma toNested_X_one : toNested (X 1) = Polynomial.C Polynomial.X := by
  change Polynomial.map (uniqueAlgEquiv ℂ (Fin 1)).toRingHom
    (finSuccEquiv ℂ 1 (X (Fin.succ (0 : Fin 1)))) = _
  rw [finSuccEquiv_X_succ]
  simp [uniqueAlgEquiv]

end CurveSymmetry

end

-- lean/GeometricRotation.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def conjugateSwap : BPoly →+* BPoly :=
  (MvPolynomial.map (starRingEnd ℂ)).comp
    (rename (Equiv.swap (0 : Fin 2) 1)).toRingHom

end CurveSymmetry

end

-- lean/RotationGroup.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- All rotations about zero preserving the whole real locus, represented by complex units. -/
noncomputable def centeredRotationGroup (P : BPoly) : Subgroup ℂˣ where
  carrier := {u | ‖(u : ℂ)‖ = 1 ∧ ∀ z : ℂ, (u : ℂ) * z ∈ realLocus P ↔ z ∈ realLocus P}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    refine ⟨by simp [hu.1, hv.1], ?_⟩
    intro z
    simpa only [Units.val_mul, mul_assoc] using (hu.2 ((v : ℂ) * z)).trans (hv.2 z)
  inv_mem' := by
    intro u hu
    refine ⟨by simpa using congrArg Inv.inv hu.1, ?_⟩
    intro z
    simpa [← mul_assoc] using (hu.2 ((↑u⁻¹ : ℂ) * z)).symm

noncomputable def rotationValue (P : BPoly) : centeredRotationGroup P →* ℂ :=
  (Units.coeHom ℂ).comp (centeredRotationGroup P).subtype

end CurveSymmetry

end

-- lean/Translation.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def lineRestriction (z v : ℂ) : BPoly →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C (fun i : Fin 2 =>
    Polynomial.C (if i = 0 then z else star z) +
      Polynomial.C (if i = 0 then v else star v) * Polynomial.X)

noncomputable def lineEquation (z v : ℂ) : BPoly :=
  C (star v) * X 0 - C v * X 1 - C (star v * z - v * star z)

end CurveSymmetry

end

-- lean/EuclideanCenter.lean
section

namespace CurveSymmetry

set_option autoImplicit false

/-- A direct Euclidean symmetry, in its complex affine form. -/
def DirectSymmetry (S : Set ℂ) (a b : ℂ) : Prop :=
  ‖a‖ = 1 ∧ ∀ z : ℂ, a * z + b ∈ S ↔ z ∈ S

end CurveSymmetry

end

-- lean/ChangeCenter.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def shift (c : ℂ) : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => X i + C (if i = 0 then c else star c))

def NotCircle (P : BPoly) : Prop :=
  ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ realLocus P = Metric.sphere c R

end CurveSymmetry

end

-- lean/DirectBound.lean
section

namespace CurveSymmetry

set_option autoImplicit false

/-- Direct Euclidean symmetries as unique affine parameters `(a,b)` for `z ↦ az+b`. -/
abbrev DirectSymmetries (P : BPoly) :=
  {ab : ℂ × ℂ // DirectSymmetry (realLocus P) ab.1 ab.2}

end CurveSymmetry

end

-- lean/Reflection.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- Pullback by the reflection `z ↦ a conjugate(z)` when `‖a‖ = 1`. -/
noncomputable def reflect (a : ℂ) : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => if i = 0 then C a * X 1 else C (star a) * X 0)

end CurveSymmetry

end

-- lean/EuclideanParameters.lean
section

namespace CurveSymmetry

set_option autoImplicit false

/-- An orientation-reversing Euclidean symmetry in complex affine coordinates. -/
def OppositeSymmetry (S : Set ℂ) (a b : ℂ) : Prop :=
  ‖a‖ = 1 ∧ ∀ z : ℂ, a * star z + b ∈ S ↔ z ∈ S

abbrev OppositeSymmetries (P : BPoly) :=
  {ab : ℂ × ℂ // OppositeSymmetry (realLocus P) ab.1 ab.2}

/-- The two possible orientations, with their unique affine parameters. -/
abbrev EuclideanSymmetries (P : BPoly) := DirectSymmetries P ⊕ OppositeSymmetries P

end CurveSymmetry

end

-- lean/FamilyQuadratic.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

lemma unit_of_reverse_unit {R : Type*} [CommRing R] [IsDomain R]
    {p : Polynomial R} (hp : p.coeff 0 ≠ 0) (hu : IsUnit p.reverse) : IsUnit p := by
  have hd := natDegree_eq_zero_of_isUnit hu
  rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hp), Nat.sub_zero] at hd
  rw [eq_C_of_natDegree_eq_zero hd] at hu ⊢
  simpa using hu

lemma irreducible_of_reverse {R : Type*} [CommRing R] [IsDomain R]
    {p : Polynomial R} (hp : p.coeff 0 ≠ 0) (hi : Irreducible p.reverse) : Irreducible p := by
  refine ⟨?_, ?_⟩
  · intro hu
    obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp hu
    apply hi.not_isUnit
    rw [← he, reverse_C]
    exact hc.map C
  · intro a b he
    have hcoeff : a.coeff 0 * b.coeff 0 ≠ 0 := by simpa [he] using hp
    have hrev : p.reverse = a.reverse * b.reverse := by rw [he, reverse_mul_of_domain]
    rcases hi.isUnit_or_isUnit hrev with ha | hb
    · exact Or.inl (unit_of_reverse_unit (mul_ne_zero_iff.mp hcoeff).1 ha)
    · exact Or.inr (unit_of_reverse_unit (mul_ne_zero_iff.mp hcoeff).2 hb)

noncomputable def familyA (m : ℕ) (α : ℂ) : UPoly := C α * X ^ m + C (star α)

noncomputable def familyB (m : ℕ) : UPoly := X * (X ^ m + 1)

/-- The strict-transform equation after the substitution `X = tY`. -/
noncomputable def familyQuadratic (m : ℕ) (α : ℂ) : NPoly :=
  C (familyA m α) + C (familyB m) * X ^ 2

noncomputable def familyReciprocal (m : ℕ) (α : ℂ) : NPoly :=
  C (familyB m) + C (familyA m α) * X ^ 2

lemma familyA_zero (m : ℕ) (hm : 0 < m) (α : ℂ) : (familyA m α).coeff 0 = star α := by
  simp [familyA, hm.ne]

lemma familyB_coeff_one (m : ℕ) (hm : 0 < m) : (familyB m).coeff 1 = 1 := by
  simp [familyB, hm.ne]

lemma familyB_ne_zero (m : ℕ) (hm : 0 < m) : familyB m ≠ 0 := by
  intro h
  have he := familyB_coeff_one m hm
  simp [h] at he

lemma family_coefficients_no_common_root {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (z : ℂ) :
    ¬ ((familyA m α).eval z = 0 ∧ (familyB m).eval z = 0) := by
  rintro ⟨hA, hB⟩
  simp only [familyA, familyB, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_one] at hA hB
  rcases mul_eq_zero.mp hB with hz | hz
  · rw [hz, zero_pow hm.ne', mul_zero, zero_add] at hA
    apply ha
    have hα : α = 0 := star_eq_zero.mp hA
    simp [hα]
  · apply ha
    linear_combination α * hz - hA

lemma familyReciprocal_primitive {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    (familyReciprocal m α).IsPrimitive := by
  intro q hq
  by_contra hu
  have hd : q.degree ≠ 0 := by
    intro hd
    exact hu (isUnit_iff_degree_eq_zero.mpr hd)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root q hd
  have hdiv := (C_dvd_iff_dvd_coeff q _).mp hq
  have hA : q ∣ familyA m α := by simpa [familyReciprocal] using hdiv 2
  have hB : q ∣ familyB m := by simpa [familyReciprocal] using hdiv 0
  apply family_coefficients_no_common_root hm ha z
  constructor
  · exact dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hz).trans hA)
  · exact dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hz).trans hB)

/-- Eisenstein at `t = 0` applies after reversing the quadratic variable. -/
theorem familyReciprocal_irreducible {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Irreducible (familyReciprocal m α) := by
  have hα : α ≠ 0 := by intro hz; apply ha; simp [hz]
  have hA : familyA m α ≠ 0 := by
    intro h
    have he := familyA_zero m hm α
    rw [h, coeff_zero] at he
    exact (star_ne_zero.mpr hα) he.symm
  have hd : (familyReciprocal m α).natDegree = 2 := by
    simp [familyReciprocal, natDegree_C_mul hA]
  have hl : (familyReciprocal m α).leadingCoeff = familyA m α := by
    rw [leadingCoeff, hd]
    simp [familyReciprocal]
  apply irreducible_of_eisenstein_criterion
    ((Ideal.span_singleton_prime (X_ne_zero : (X : UPoly) ≠ 0)).mpr prime_X)
  · rw [hl, Ideal.mem_span_singleton, X_dvd_iff, familyA_zero m hm α]
    exact star_ne_zero.mpr hα
  · intro n hn
    have hn' : n < 2 := by simpa [hd] using (coe_lt_degree.mp hn)
    interval_cases n
    · rw [Ideal.mem_span_singleton]
      simp [familyReciprocal, familyB]
    · simp [familyReciprocal]
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have hc := X_pow_dvd_iff.mp h 1 (by decide : 1 < 2)
    simp [familyReciprocal, familyB_coeff_one m hm] at hc
  · exact familyReciprocal_primitive hm ha

/-- The quadratic strict transform of every nonreal-parameter family member is irreducible.
The blowup-to-original-curve transfer is a separate proof obligation. -/
theorem familyQuadratic_irreducible {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Irreducible (familyQuadratic m α) := by
  have hα : α ≠ 0 := by intro hz; apply ha; simp [hz]
  have hA : familyA m α ≠ 0 := by
    intro h
    have he := familyA_zero m hm α
    rw [h, coeff_zero] at he
    exact (star_ne_zero.mpr hα) he.symm
  have h0 : (familyQuadratic m α).coeff 0 ≠ 0 := by simpa [familyQuadratic] using hA
  have hrev : (familyQuadratic m α).reverse = familyReciprocal m α := by
    have hX : ((X : NPoly) ^ 2).reverse = 1 := by
      have hone : (1 : NPoly).reverse = 1 := by
        change (C (1 : UPoly)).reverse = C 1
        rw [reverse_C]
      simpa [hone] using (reverse_mul_X_pow (1 : NPoly) 2)
    simp [familyQuadratic, familyReciprocal, reverse_C_add,
      natDegree_C_mul (familyB_ne_zero m hm), hX, add_comm]
  exact irreducible_of_reverse h0 (hrev ▸ familyReciprocal_irreducible hm ha)

end CurveSymmetry

end


