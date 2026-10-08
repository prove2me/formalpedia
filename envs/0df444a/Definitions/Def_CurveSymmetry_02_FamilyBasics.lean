-- Prove2me | Definitions.Def_CurveSymmetry_02_FamilyBasics
-- name    : CurveSymmetry_02_FamilyBasics
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:10:37.741499+00:00
-- url     : https://prove2.me/theorems/26e6750d-f64e-4a59-b95a-5deb41fec390
-- title:
--   Cartesian equations and their isometry groups, the extremal polynomial $P_\alpha$, Fermat curves and the chart $X=tY$
-- statement:
--   Let $\mathbb R[x,y]$ and $\mathbb C[X,Y]$ be the real and complex polynomial rings in two variables. The real plane is $\mathbb C$, with $z=x+iy$, and $\mathbb C[X,Y]$ is read in the coordinates $X=z$, $Y=\bar z$, so that $Z(P)=\{z\in\mathbb C : P(z,\bar z)=0\}$ is the real locus of $P$. Write $\mathrm{Isom}(\mathbb C)$ for the group of all distance-preserving bijections of $\mathbb C$. Throughout, $m,d\in\mathbb N$ and $\alpha,a,b,c\in\mathbb C$.
--
--   For a real polynomial $f\in\mathbb R[x,y]$ and a set $S\subseteq\mathbb C$, the file defines the zero set of $f$ in the plane and the symmetry group of $S$:
--   $$C_f=\{z\in\mathbb C : f(\operatorname{Re}z,\operatorname{Im}z)=0\},\qquad \mathrm{Sym}(S)=\{T\in\mathrm{Isom}(\mathbb C) : T(z)\in S\iff z\in S\ \text{for all}\ z\in\mathbb C\}.$$
--   It also defines:
--
--   1. Geometric irreducibility of $f$, meaning that $f$ is irreducible in $\mathbb C[x,y]$; and the direct symmetry pairs of $C_f$, the $(a,b)$ with $|a|=1$ and $az+b\in C_f\iff z\in C_f$ for all $z$.
--   2. The passage to the coordinates of the note, as substitutions in the polynomial ring in two variables: $f(x,y)\mapsto f\big(\tfrac{X+Y}{2},\tfrac{X-Y}{2i}\big)$ and its inverse $P(X,Y)\mapsto P(x+iy,\,x-iy)$; the complexification of a real $f$, which is its image under the former once its coefficients are viewed in $\mathbb C$; and the real polynomial formed by the real parts of the coefficients of a complex one.
--   3. The group $\mathrm{Sym}(Z(P))$; the isometries $z\mapsto az+b$ and $z\mapsto a\bar z+b$ for $|a|=1$; and the map sending a direct or opposite symmetry pair $(a,b)$ of $Z(P)$ to the corresponding element of $\mathrm{Sym}(Z(P))$.
--   4. The extremal polynomial of equation (6), $P_\alpha=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$, for which $P_\alpha(z,\bar z)=2\operatorname{Re}\big(z^m(|z|^2+\alpha)\big)$, and the two-parameter polynomial $X^m(a+bXY)+Y^m(\bar a+\bar bXY)$, the radial form (5) with $A(s)=a+bs$.
--   5. The Fermat polynomial $X^d+Y^d-2$, also written as an element of $\mathbb C[Y][X]$.
--   6. The dilation pullback $P(X,Y)\mapsto P(cX,\bar cY)$ along $z\mapsto cz$, and the blow-up substitution $P(X,Y)\mapsto P(tY,Y)$, whose target coordinates are $(Y,t)$.
--
--   Theorem 1 is formalized for a real polynomial $f$: its curve $C$ is $C_f$, irreducibility over $\mathbb C$ is geometric irreducibility, and $\mathrm{Sym}(C)$ is the group of all isometries of the plane preserving $C_f$; the substitution $f\mapsto P$ is the passage to the polynomial $P$ that precedes equation (4). $P_\alpha$ is the complexification (6) of the curves $C_{m,\alpha}$ of Theorems 1 and 2 and Lemma 4. $X^d+Y^d-2$ is the complexification of $2(\operatorname{Re}(z^d)-1)$, that is, of the sharpness examples $\operatorname{Re}(z^d)=1$ of Theorem 1 and of the degree-four curve of Remark 5. The two-parameter polynomial and the dilation pullback express the radial form (5) and the normalization $z=re^{i\phi}w$ in the equality case of Theorem 1, and dilations also enter the coefficient comparison (8) in the proof of Theorem 2. The blow-up substitution is the chart $X=tY$ of the proof of Lemma 4.
--
--   **Formalization Note**: Isometries are elements of `ℂ ≃ᵢ ℂ`, with no affine form assumed, and real polynomials are `MvPolynomial (Fin 2) ℝ`. The file also proves the facts later parts use: if $P$ is not a unit, is not divisible by $Y$, and $P(tY,Y)=Y^mH$ with $H$ irreducible, then $P$ is irreducible; $P_\alpha$ has total degree $m+2$ for $m\ge1$ and is irreducible when moreover $\alpha\ne\bar\alpha$; and $X^d+Y^d-2$ is irreducible for $d\ge1$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules Blowup, FamilyIrreducibility, FamilyRotations, Fermat, EqualityForm, Normalization, IsometryInterface, CartesianCoordinates, CartesianReal, CartesianDescent in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 02 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

-- lean/Blowup.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- Substitution `(X,Y) ↦ (tY,Y)`, with target coordinates ordered `(Y,t)`. -/
noncomputable def blowup : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => if i = 0 then X 1 * X 0 else X 0)

lemma blowup_monomial (s : Exponent) (c : ℂ) :
    blowup (monomial s c) = monomial (exponent (s 0 + s 1) (s 0)) c := by
  simp only [blowup, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, monomial_exponent]
  rw [pow_add, mul_pow]
  ring

lemma coeff_blowup (P : BPoly) (a b : ℕ) :
    (blowup P).coeff (exponent (a + b) a) = P.coeff (exponent a b) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s c =>
      rw [blowup_monomial]
      have he : exponent (s 0 + s 1) (s 0) = exponent (a + b) a ↔ s = exponent a b := by
        simp only [exponent_eq_iff, exponent_zero, exponent_one]
        omega
      simp [coeff_monomial, he]
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ]

lemma blowup_injective : Function.Injective blowup := by
  intro P Q he
  ext s
  have hs : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  rw [hs]
  exact (coeff_blowup P (s 0) (s 1)).symm.trans
    ((congrArg (fun R : BPoly => R.coeff (exponent (s 0 + s 1) (s 0))) he).trans
      (coeff_blowup Q (s 0) (s 1)))

lemma unit_of_blowup_dvd_power {P : BPoly} (hY : ¬ (X 1 : BPoly) ∣ P)
    {m : ℕ} (hdiv : blowup P ∣ (X 0 : BPoly) ^ m) : IsUnit P := by
  rw [X_pow_eq_monomial] at hdiv
  obtain ⟨s, c, hs, hc, he⟩ := dvd_monomial_one_iff_exists.mp hdiv
  have hs1 : s 1 = 0 := by
    have h := hs 1
    simpa using h
  have hP : P = C c * X 1 ^ s 0 := by
    apply blowup_injective
    rw [he]
    have hs' : s = exponent (s 0) 0 := exponent_eq_iff.mpr ⟨rfl, hs1⟩
    rw [hs', monomial_exponent]
    simp [blowup]
  by_cases hzero : s 0 = 0
  · rw [hP, hzero, pow_zero, mul_one]
    exact hc.map C
  · exfalso
    apply hY
    rw [hP]
    exact (dvd_pow_self (X 1 : BPoly) hzero).mul_left _

/-- Removing the exceptional coordinate factor from an irreducible strict transform
preserves irreducibility of the original equation. -/
theorem irreducible_of_blowup {P H : BPoly} {m : ℕ}
    (hunit : ¬ IsUnit P) (hY : ¬ (X 1 : BPoly) ∣ P) (hH : Irreducible H)
    (he : blowup P = (X 0 : BPoly) ^ m * H) : Irreducible P := by
  refine ⟨hunit, ?_⟩
  intro A B hAB
  have hd : H ∣ blowup A * blowup B := by
    rw [← map_mul, ← hAB, he]
    exact dvd_mul_left H _
  have hprime : Prime H := UniqueFactorizationMonoid.irreducible_iff_prime.mp hH
  have hY_A : ¬ (X 1 : BPoly) ∣ A := fun h => hY (hAB ▸ h.mul_right B)
  have hY_B : ¬ (X 1 : BPoly) ∣ B := fun h => hY (hAB ▸ h.mul_left A)
  rcases hprime.dvd_or_dvd hd with hA | hB
  · obtain ⟨Q, hQ⟩ := hA
    have hmul : (X 0 : BPoly) ^ m = Q * blowup B := by
      apply mul_left_cancel₀ hH.ne_zero
      have h := he
      rw [hAB, map_mul, hQ] at h
      linear_combination -h
    exact Or.inr (unit_of_blowup_dvd_power hY_B ⟨Q, by rw [hmul, mul_comm]⟩)
  · obtain ⟨Q, hQ⟩ := hB
    have hmul : (X 0 : BPoly) ^ m = Q * blowup A := by
      apply mul_left_cancel₀ hH.ne_zero
      have h := he
      rw [hAB, map_mul, hQ] at h
      linear_combination -h
    exact Or.inl (unit_of_blowup_dvd_power hY_A ⟨Q, by rw [hmul, mul_comm]⟩)

end CurveSymmetry

end

-- lean/FamilyIrreducibility.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- Complexification of twice `Re(z^m (|z|^2 + α))`. -/
noncomputable def familyPolynomial (m : ℕ) (α : ℂ) : BPoly :=
  X 0 ^ m * (C α + X 0 * X 1) + X 1 ^ m * (C (star α) + X 0 * X 1)

lemma familyPolynomial_not_isUnit {m : ℕ} (hm : 0 < m) (α : ℂ) :
    ¬ IsUnit (familyPolynomial m α) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun _ : Fin 2 => (0 : ℂ)))
  simp [familyPolynomial, hm.ne'] at h

lemma familyPolynomial_not_dvd_Y {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ 0) :
    ¬ (X 1 : BPoly) ∣ familyPolynomial m α := by
  intro h
  have he := map_dvd (eval₂Hom (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then 1 else 0)) h
  simp [familyPolynomial, hm.ne', ha] at he

lemma familyPolynomial_blowup (m : ℕ) (α : ℂ) :
    blowup (familyPolynomial m α) = (X 0 : BPoly) ^ m * toNested.symm (familyQuadratic m α) := by
  apply toNested.injective
  simp only [familyPolynomial, map_add, map_mul, map_pow]
  have h0 : blowup (X 0) = X 1 * X 0 := by simp [blowup]
  have h1 : blowup (X 1) = X 0 := by simp [blowup]
  have hC : ∀ c : ℂ, blowup (C c) = C c := by intro c; simp [blowup]
  rw [h0, h1, hC, hC, toNested.apply_symm_apply]
  simp only [map_mul, toNested_C, toNested_X_zero, toNested_X_one,
    familyQuadratic, familyA, familyB, map_add, map_pow, map_one]
  ring

/-- Every nonreal-parameter family polynomial is geometrically irreducible.
The proof works already for `m ≥ 1` and does not need modulus one. -/
theorem familyPolynomial_irreducible {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Irreducible (familyPolynomial m α) := by
  have hα : α ≠ 0 := by intro h; apply ha; simp [h]
  exact irreducible_of_blowup (familyPolynomial_not_isUnit hm α)
    (familyPolynomial_not_dvd_Y hm hα)
    ((familyQuadratic_irreducible hm ha).map toNested.symm.toMulEquiv)
    (familyPolynomial_blowup m α)

end CurveSymmetry

end

-- lean/FamilyRotations.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

lemma family_monomial_form (m : ℕ) (α : ℂ) :
    familyPolynomial m α = monomial (exponent m 0) α + monomial (exponent (m + 1) 1) 1 +
      monomial (exponent 0 m) (star α) + monomial (exponent 1 (m + 1)) 1 := by
  simp only [familyPolynomial, monomial_exponent, pow_zero, C_1, pow_succ]
  ring

theorem family_degree {m : ℕ} (hm : 0 < m) (α : ℂ) :
    (familyPolynomial m α).totalDegree = m + 2 := by
  have hc : (familyPolynomial m α).coeff (exponent (m + 1) 1) = 1 := by
    rw [family_monomial_form]
    have h0 : exponent m 0 ≠ exponent (m + 1) 1 := by simp [exponent_eq_iff]
    have h1 : exponent 0 m ≠ exponent (m + 1) 1 := by simp [exponent_eq_iff]
    have h2 : exponent 1 (m + 1) ≠ exponent (m + 1) 1 := by simp [exponent_eq_iff]; omega
    simp [coeff_monomial, h0, h1, h2]
  have hlo := support_degree (mem_support_iff.mpr (by rw [hc]; exact one_ne_zero))
  simp only [exponent_zero, exponent_one] at hlo
  let A : BPoly := monomial (exponent m 0) α
  let B : BPoly := monomial (exponent (m + 1) 1) 1
  let D : BPoly := monomial (exponent 0 m) (star α)
  let E : BPoly := monomial (exponent 1 (m + 1)) 1
  have hA : A.totalDegree ≤ m := by
    simpa [A, Function.id_def, exponent_degree] using totalDegree_monomial_le (exponent m 0) α
  have hB : B.totalDegree ≤ m + 2 := by
    simp [B, totalDegree_monomial, exponent_degree, Nat.add_assoc]
  have hD : D.totalDegree ≤ m := by
    simpa [D, Function.id_def, exponent_degree] using totalDegree_monomial_le (exponent 0 m) (star α)
  have hE : E.totalDegree ≤ m + 2 := by
    simp [E, totalDegree_monomial, exponent_degree, Nat.add_left_comm]
  have hab := totalDegree_add A B
  have habd := totalDegree_add (A + B) D
  have habde := totalDegree_add (A + B + D) E
  have he : familyPolynomial m α = A + B + D + E := family_monomial_form m α
  rw [he] at hlo ⊢
  omega

end CurveSymmetry

end

-- lean/Fermat.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

noncomputable def fermatNested (d : ℕ) : NPoly := X ^ d + C (X ^ d - C 2)

theorem fermatNested_irreducible {d : ℕ} (hd : 0 < d) : Irreducible (fermatNested d) := by
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) hd
  have hn : η ≠ 0 := by intro h; simp [h, hd.ne'] at hη
  have hmonic : (fermatNested d).Monic := monic_X_pow_add_C _ hd.ne'
  have hdeg : (fermatNested d).natDegree = d := by
    simp only [fermatNested, natDegree_add_C, natDegree_X_pow]
  have hprime : (Ideal.span ({X - C η} : Set UPoly)).IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero η)).mpr (prime_X_sub_C η)
  apply irreducible_of_eisenstein_criterion hprime
  · rw [hmonic.leadingCoeff]
    exact fun h => hprime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro n hnd
    have hnd' : n < d := by simpa [hdeg] using coe_lt_degree.mp hnd
    rw [Ideal.mem_span_singleton]
    by_cases h0 : n = 0
    · subst n
      simp only [fermatNested, coeff_add, coeff_X_pow, hd.ne, ite_false, coeff_C_zero, zero_add]
      apply dvd_iff_isRoot.mpr
      simp [IsRoot, hη]
    · simp only [fermatNested, coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hnd'),
        coeff_C, if_neg h0, add_zero, dvd_zero]
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hs
    have hc : (fermatNested d).coeff 0 = X ^ d - C 2 := by
      simp only [fermatNested, coeff_add, coeff_X_pow, if_neg hd.ne, coeff_C_zero, zero_add]
    rw [hc] at hs
    have ht := pow_sub_one_dvd_derivative_of_pow_dvd hs
    simp only [show 2 - 1 = 1 by decide, pow_one] at ht
    have he := dvd_iff_isRoot.mp ht
    have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp [IsRoot, derivative_X_pow, hdn, hn] at he
  · exact hmonic.isPrimitive

noncomputable def fermatPolynomial (d : ℕ) : BPoly :=
  MvPolynomial.X 0 ^ d + MvPolynomial.X 1 ^ d - MvPolynomial.C 2

lemma fermat_toNested (d : ℕ) : toNested (fermatPolynomial d) = fermatNested d := by
  simp [fermatPolynomial, fermatNested, toNested_X_zero, toNested_X_one, toNested_C]
  ring

theorem fermat_irreducible {d : ℕ} (hd : 0 < d) : Irreducible (fermatPolynomial d) := by
  have h := (fermatNested_irreducible hd).map toNested.symm.toMulEquiv
  change Irreducible (toNested.symm (fermatNested d)) at h
  rwa [← fermat_toNested, toNested.symm_apply_apply] at h

end CurveSymmetry

end

-- lean/EqualityForm.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def twoParameter (m : ℕ) (a b : ℂ) : BPoly :=
  X 0 ^ m * (C a + C b * X 0 * X 1) +
    X 1 ^ m * (C (star a) + C (star b) * X 0 * X 1)

end CurveSymmetry

end

-- lean/Normalization.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- Pullback by the direct similarity `z ↦ cz`, allowing arbitrary nonzero scale. -/
noncomputable def dilate (c : ℂ) : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => C (if i = 0 then c else star c) * X i)

end CurveSymmetry

end

-- lean/IsometryInterface.lean
section

namespace CurveSymmetry

set_option autoImplicit false

/-- The subgroup of actual Mathlib isometries preserving the entire curve. -/
def isometrySetGroup (S : Set ℂ) : Subgroup (ℂ ≃ᵢ ℂ) where
  carrier := {f | ∀ z : ℂ, f z ∈ S ↔ z ∈ S}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg z
    exact (hf (g z)).trans (hg z)
  inv_mem' := by
    intro f hf z
    simpa using (hf (f⁻¹ z)).symm

abbrev isometrySymmetryGroup (P : BPoly) := isometrySetGroup (realLocus P)

noncomputable def affineDirectIsometry (a b : ℂ) (ha : ‖a‖ = 1) : ℂ ≃ᵢ ℂ :=
  (rotation ⟨a, by simpa [Submonoid.unitSphere] using ha⟩).toIsometryEquiv.trans (IsometryEquiv.addRight b)

@[simp] lemma affineDirectIsometry_apply (a b : ℂ) (ha : ‖a‖ = 1) (z : ℂ) :
    affineDirectIsometry a b ha z = a * z + b := rfl

noncomputable def affineOppositeIsometry (a b : ℂ) (ha : ‖a‖ = 1) : ℂ ≃ᵢ ℂ :=
  Complex.conjLIE.toIsometryEquiv.trans (affineDirectIsometry a b ha)

@[simp] lemma affineOppositeIsometry_apply (a b : ℂ) (ha : ‖a‖ = 1) (z : ℂ) :
    affineOppositeIsometry a b ha z = a * star z + b := rfl

noncomputable def parametersToIsometry (P : BPoly) : EuclideanSymmetries P → isometrySymmetryGroup P
  | Sum.inl u => ⟨affineDirectIsometry u.val.1 u.val.2 u.prop.1, u.prop.2⟩
  | Sum.inr u => ⟨affineOppositeIsometry u.val.1 u.val.2 u.prop.1, u.prop.2⟩

end CurveSymmetry

end

-- lean/CartesianCoordinates.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def complexify : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => if i = 0 then C (1 / 2 : ℂ) * (X 0 + X 1)
    else -C Complex.I * C (1 / 2 : ℂ) * (X 0 - X 1))

noncomputable def cartesianize : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => if i = 0 then X 0 + C Complex.I * X 1
    else X 0 - C Complex.I * X 1)

end CurveSymmetry

end

-- lean/CartesianReal.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

abbrev RPoly := MvPolynomial (Fin 2) ℝ

noncomputable def complexifyReal (f : RPoly) : BPoly :=
  complexify (map Complex.ofRealHom f)

def cartesianLocus (f : RPoly) : Set ℂ :=
  {z | eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f = 0}

/-- Geometric irreducibility, not just irreducibility over the reals. -/
def GeometricallyIrreducible (f : RPoly) : Prop :=
  Irreducible (map Complex.ofRealHom f)

abbrev CartesianDirectSymmetries (f : RPoly) :=
  {ab : ℂ × ℂ // DirectSymmetry (cartesianLocus f) ab.1 ab.2}

end CurveSymmetry

end

-- lean/CartesianDescent.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def realCoefficients (P : BPoly) : RPoly :=
  .ofCoeff (Finsupp.mapRange Complex.re (by simp) (AddMonoidAlgebra.coeff P))

end CurveSymmetry

end


