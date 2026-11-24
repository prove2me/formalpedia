-- Prove2me | Definitions.Def_HodgeComputerFormal_FiniteDiff
-- name    : HodgeComputerFormal_FiniteDiff
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:23:03.465805+00:00
-- url     : https://prove2.me/theorems/20965e8d-29f1-41b0-8fb1-d2a110286c6c
-- title:
--   Extending derivations across finite separable field extensions
-- statement:
--   Core construction for uniquely lifting $\mathbb{Z}$-derivations across finite extensions $L / K$ of characteristic-zero fields (`HoldoutConstruction.extendFiniteDerivation`):
--
--   Given $D \in \operatorname{Der}_{\mathbb{Z}}(K, K)$, every element $\alpha \in L$ is algebraic over $K$ with separable minimal polynomial $m_\alpha(X) \in K[X]$ satisfying $m_\alpha'(\alpha) \neq 0$, uniquely fixing $E(\alpha) = -(D^{\mathrm{coeff}} m_\alpha)(\alpha) / m_\alpha'(\alpha)$. The module constructs `extendFiniteDerivation`, proves its compatibility with $\operatorname{algebraMap}(K, L)$, and proves that commuting derivations on $K$ lift to commuting derivations on $L$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/HoldoutCover/FiniteDifferentials.lean

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/- Source component: FieldValuedFraction -/
section
/-!
Field-valued derivations extend to a fraction field.

This adapts the quotient-rule construction in the accepted
`data/quadric-contact-broken/FractionDerivation.lean`, allowing the original
derivation to take values in the fraction field instead of the polynomial
ring. Credit belongs to that contribution and the Lean/mathlib authors.
Prepared with OpenAI ChatGPT assistance for a contribution through GitHub
account fqlx. This is generic algebra, not a `HasCertificate` assertion.
-/

noncomputable section
namespace HoldoutConstruction.FieldValuedFraction
variable {P F : Type*} [CommRing P] [IsDomain P] [Field F]
  [Algebra P F] [IsFractionRing P F]

private def num (x : F) : P := Classical.choose (IsFractionRing.div_surjective P x)
private def den (x : F) : P := Classical.choose (Classical.choose_spec (IsFractionRing.div_surjective P x))
omit [IsDomain P] in
private theorem den_mem (x : F) : den (P := P) x ∈ nonZeroDivisors P :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective P x))).1
omit [IsDomain P] in
private theorem repr_eq (x : F) :
    algebraMap P F (num x) / algebraMap P F (den x) = x :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective P x))).2
private theorem den_ne (x : F) : algebraMap P F (den x) ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den_mem x)
private theorem map_ne {x : P} (hx : x ≠ 0) : algebraMap P F x ≠ 0 := by
  exact fun h => hx ((IsFractionRing.injective P F) (by simpa using h))

private def quotientD (D : Derivation ℤ P F) (x : F) : F :=
  (D (num x) * algebraMap P F (den x) -
    algebraMap P F (num x) * D (den x)) /
    algebraMap P F (den x) ^ 2

private theorem quotientD_div (D : Derivation ℤ P F) (a b : P) (hb : b ≠ 0) :
    quotientD D (algebraMap P F a / algebraMap P F b) =
      (D a * algebraMap P F b -
        algebraMap P F a * D b) / algebraMap P F b ^ 2 := by
  let x := algebraMap P F a / algebraMap P F b
  have hd := den_ne (P := P) x
  have hb' := map_ne (F := F) hb
  have hcross : num x * b = a * den x := by
    apply IsFractionRing.injective P F
    simpa only [map_mul] using (div_eq_div_iff hd hb').mp (repr_eq (P := P) x)
  have hdcross := congrArg D hcross
  simp only [Derivation.leibniz, Algebra.smul_def] at hdcross
  have hcross' := congrArg (algebraMap P F) hcross
  simp only [map_mul] at hcross'
  change (D (num x) * algebraMap P F (den x) -
    algebraMap P F (num x) * D (den x)) /
    algebraMap P F (den x)^2 = _
  field_simp
  linear_combination
    algebraMap P F (den x) * algebraMap P F b * hdcross -
    (algebraMap P F b * D (den x) +
      algebraMap P F (den x) * D b) * hcross'

private theorem quotientD_map (D : Derivation ℤ P F) (a : P) :
    quotientD D (algebraMap P F a) = D a := by
  have h := quotientD_div (F := F) D a 1 one_ne_zero
  simpa using h

private theorem quotientD_add (D : Derivation ℤ P F) (x y : F) :
    quotientD D (x+y) = quotientD D x + quotientD D y := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective P x
  obtain ⟨c,d,hd,rfl⟩ := IsFractionRing.div_surjective P y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb' := map_ne (F := F) hb0
  have hd' := map_ne (F := F) hd0
  have he : algebraMap P F a / algebraMap P F b + algebraMap P F c / algebraMap P F d =
      algebraMap P F (a*d+c*b) / algebraMap P F (b*d) := by
    simp only [map_add, map_mul]
    field_simp
  rw [he, quotientD_div D _ _ (mul_ne_zero hb0 hd0), quotientD_div D _ _ hb0,
    quotientD_div D _ _ hd0]
  simp only [map_add, map_mul, Derivation.leibniz, Algebra.smul_def]
  field_simp
  ring

private theorem quotientD_mul (D : Derivation ℤ P F) (x y : F) :
    quotientD D (x*y) = x * quotientD D y + y * quotientD D x := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective P x
  obtain ⟨c,d,hd,rfl⟩ := IsFractionRing.div_surjective P y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb' := map_ne (F := F) hb0
  have hd' := map_ne (F := F) hd0
  have he : algebraMap P F a / algebraMap P F b * (algebraMap P F c / algebraMap P F d) =
      algebraMap P F (a*c) / algebraMap P F (b*d) := by
    simp only [map_mul, mul_div_mul_comm]
  rw [he, quotientD_div D _ _ (mul_ne_zero hb0 hd0), quotientD_div D _ _ hb0,
    quotientD_div D _ _ hd0]
  simp only [map_mul, Derivation.leibniz, Algebra.smul_def]
  field_simp
  ring

/-- A fraction-field-valued derivation extends uniquely to the fraction field.
Its action is proved from the quotient rule; no derivative of a chosen
representative is assumed. -/
def extend (D : Derivation ℤ P F) : Derivation ℤ F F :=
  Derivation.mk'
    ({ toFun := quotientD D
       map_zero' := by simpa using quotientD_map (F := F) D 0
       map_add' := quotientD_add D } : F →+ F).toIntLinearMap
    (by intro x y; exact quotientD_mul D x y)

@[simp] theorem extend_map (D : Derivation ℤ P F) (a : P) :
    extend (F := F) D (algebraMap P F a) = D a :=
  quotientD_map D a

theorem extend_div (D : Derivation ℤ P F) (a b : P) (hb : b ≠ 0) :
    extend (F := F) D (algebraMap P F a / algebraMap P F b) =
      (D a * algebraMap P F b -
        algebraMap P F a * D b) / algebraMap P F b ^ 2 :=
  quotientD_div D a b hb

omit [IsDomain P] in
/-- A derivation on a fraction field is determined by its values on the
original domain. -/
theorem derivation_ext (D E : Derivation ℤ F F)
    (agree : ∀ a : P, D (algebraMap P F a) = E (algebraMap P F a)) : D = E := by
  ext x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective P x
  rw [Derivation.leibniz_div, Derivation.leibniz_div, agree a, agree b]

/-- Uniqueness of the extension constructed by the quotient rule. -/
theorem extend_unique (D : Derivation ℤ P F) (E : Derivation ℤ F F)
    (compatible : ∀ a, E (algebraMap P F a) = D a) : E = extend D := by
  apply derivation_ext (P := P)
  intro a
  rw [compatible, extend_map]

end HoldoutConstruction.FieldValuedFraction
end
end

/- Source component: FiniteDerivationExtension -/
section
/-!
Unique extension and commutation of derivations through finite field
extensions in characteristic zero. Prepared with OpenAI ChatGPT assistance
for a contribution through GitHub account fqlx. The underlying extension
and uniqueness theorems are credited to the Lean/mathlib authors.
-/

noncomputable section

namespace HoldoutConstruction

open Differential

variable {K L : Type*} [Field K] [Field L] [CharZero K]
variable [Algebra K L] [FiniteDimensional K L]

/-- The canonical chosen extension supplied by the finite differential-field
construction in mathlib. -/
def extendFiniteDerivation (D : Derivation ℤ K K) : Derivation ℤ L L :=
  let : Differential K := ⟨D⟩
  (Differential.differentialFiniteDimensional K L).deriv

theorem extendFiniteDerivation_apply (D : Derivation ℤ K K) (x : K) :
    extendFiniteDerivation (L := L) D (algebraMap K L x) = algebraMap K L (D x) := by
  let : Differential K := ⟨D⟩
  let : Differential L := Differential.differentialFiniteDimensional K L
  let : DifferentialAlgebra K L := Differential.differentialAlgebraFiniteDimensional
  exact deriv_algebraMap x

/-- A finite extension in characteristic zero has at most one derivation
extending any specified base derivation. -/
theorem finite_derivation_unique
    (D : Derivation ℤ K K) (E E' : Derivation ℤ L L)
    (compatible : ∀ x, E (algebraMap K L x) = algebraMap K L (D x))
    (compatible' : ∀ x, E' (algebraMap K L x) = algebraMap K L (D x)) : E = E' := by
  let : Differential K := ⟨D⟩
  let : Unique {_δ : Differential L // DifferentialAlgebra K L} :=
    Differential.uniqueDifferentialAlgebraFiniteDimensional
  let δ : {_δ : Differential L // DifferentialAlgebra K L} :=
    ⟨⟨E⟩, by
      let : Differential L := ⟨E⟩
      exact ⟨compatible⟩⟩
  let δ' : {_δ : Differential L // DifferentialAlgebra K L} :=
    ⟨⟨E'⟩, by
      let : Differential L := ⟨E'⟩
      exact ⟨compatible'⟩⟩
  have h : δ = δ' := Subsingleton.elim _ _
  exact congrArg (fun δ => δ.1.deriv) h

/-- Compatible finite-field lifts of commuting derivations commute. -/
theorem finite_derivations_commute
    (D₁ D₂ : Derivation ℤ K K) (E₁ E₂ : Derivation ℤ L L)
    (compatible₁ : ∀ x, E₁ (algebraMap K L x) = algebraMap K L (D₁ x))
    (compatible₂ : ∀ x, E₂ (algebraMap K L x) = algebraMap K L (D₂ x))
    (commute : Function.Commute D₁ D₂) : Function.Commute E₁ E₂ := by
  have hbracket : ⁅E₁, E₂⁆ = (0 : Derivation ℤ L L) := by
    apply finite_derivation_unique (0 : Derivation ℤ K K)
    · intro x
      simp only [Derivation.commutator_apply, compatible₁, compatible₂,
        commute x, sub_self, Derivation.zero_apply, map_zero]
    · intro x
      simp only [Derivation.zero_apply, map_zero]
  intro x
  have h := congrArg (fun E : Derivation ℤ L L => E x) hbracket
  simpa only [Derivation.commutator_apply, Derivation.zero_apply, sub_eq_zero] using h

theorem extendFiniteDerivation_commute (D₁ D₂ : Derivation ℤ K K)
    (commute : Function.Commute D₁ D₂) :
    Function.Commute (extendFiniteDerivation (L := L) D₁)
      (extendFiniteDerivation (L := L) D₂) :=
  finite_derivations_commute D₁ D₂ _ _ (extendFiniteDerivation_apply D₁)
    (extendFiniteDerivation_apply D₂) commute

end HoldoutConstruction

end
end

/- Source component: PolynomialDifferentials -/
section
/-!
Commuting coordinate derivations for a polynomial curve parameter over an
algebraic coefficient field. Coefficient derivatives act coefficientwise;
the curve derivative fixes every coefficient. Both extend by the proved
quotient rule and preserve the polynomial subring of the function field.
-/

noncomputable section

namespace HoldoutConstruction

section RingFraction

variable {P L : Type*} [CommRing P] [IsDomain P] [Field L]
variable [Algebra P L] [IsFractionRing P L]

def extendRingDerivation (D : Derivation ℤ P P) : Derivation ℤ L L :=
  FieldValuedFraction.extend ((Algebra.linearMap P L).compDer D)

@[simp] theorem extendRingDerivation_apply (D : Derivation ℤ P P) (p : P) :
    extendRingDerivation (L := L) D (algebraMap P L p) = algebraMap P L (D p) := by
  rw [extendRingDerivation, FieldValuedFraction.extend_map]
  rfl

theorem extendRingDerivation_commute (D E : Derivation ℤ P P)
    (h : Function.Commute D E) :
    Function.Commute (extendRingDerivation (L := L) D) (extendRingDerivation (L := L) E) := by
  have hz : ⁅extendRingDerivation (L := L) D, extendRingDerivation (L := L) E⁆ = 0 := by
    apply FieldValuedFraction.derivation_ext (P := P) (F := L)
    intro p
    simp only [Derivation.commutator_apply, extendRingDerivation_apply, h p,
      sub_self, Derivation.zero_apply]
  intro x
  have h := congrArg (fun δ : Derivation ℤ L L => δ x) hz
  simpa only [Derivation.commutator_apply, Derivation.zero_apply,
    sub_eq_zero] using h

theorem extendRingDerivation_mem_range (D : Derivation ℤ P P) (x : L)
    (hx : x ∈ (algebraMap P L).range) :
    extendRingDerivation D x ∈ (algebraMap P L).range := by
  obtain ⟨p,rfl⟩ := hx
  exact ⟨D p, (extendRingDerivation_apply D p).symm⟩

end RingFraction

section Polynomial

variable {E : Type*} [CommRing E]

def coefficientPolynomialDerivation (D : Derivation ℤ E E) :
    Derivation ℤ (Polynomial E) (Polynomial E) :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp] theorem coefficientPolynomialDerivation_coeff
    (D : Derivation ℤ E E) (p : Polynomial E) (n : ℕ) :
    (coefficientPolynomialDerivation D p).coeff n = D (p.coeff n) := rfl

@[simp] theorem coefficientPolynomialDerivation_C (D : Derivation ℤ E E) (a : E) :
    coefficientPolynomialDerivation D (Polynomial.C a) = Polynomial.C (D a) := by
  ext n
  by_cases hn : n=0 <;> simp [Polynomial.coeff_C, hn]

@[simp] theorem coefficientPolynomialDerivation_X (D : Derivation ℤ E E) :
    coefficientPolynomialDerivation D (Polynomial.X : Polynomial E) = 0 := by
  ext n
  simp [Polynomial.coeff_X, apply_ite]

def timePolynomialDerivation : Derivation ℤ (Polynomial E) (Polynomial E) :=
  (Polynomial.derivative' : Derivation E (Polynomial E) (Polynomial E)).restrictScalars ℤ

@[simp] theorem timePolynomialDerivation_apply (p : Polynomial E) :
    timePolynomialDerivation p = p.derivative := rfl

theorem coefficientPolynomialDerivation_commute (D E' : Derivation ℤ E E)
    (h : Function.Commute D E') :
    Function.Commute (coefficientPolynomialDerivation D)
      (coefficientPolynomialDerivation E') := by
  intro p
  ext n
  exact h (p.coeff n)

theorem time_coefficientPolynomialDerivation_commute (D : Derivation ℤ E E) :
    Function.Commute timePolynomialDerivation (coefficientPolynomialDerivation D) := by
  intro p
  ext n
  simp only [timePolynomialDerivation_apply, Polynomial.coeff_derivative,
    coefficientPolynomialDerivation_coeff, Derivation.leibniz, smul_eq_mul,
    map_add, Derivation.map_natCast, Derivation.map_one_eq_zero, zero_add,
    mul_zero, add_zero]
  exact mul_comm _ _

end Polynomial

section FunctionField

variable {E : Type*} [Field E]

abbrev CurveFunctionField (E : Type*) [Field E] := FractionRing (Polynomial E)

local instance : Algebra ℤ (CurveFunctionField E) := Ring.toIntAlgebra _

def curveTime : CurveFunctionField E :=
  algebraMap (Polynomial E) (CurveFunctionField E) Polynomial.X

def curveTimeDerivation : Derivation ℤ (CurveFunctionField E) (CurveFunctionField E) :=
  extendRingDerivation (P := Polynomial E) (L := CurveFunctionField E)
    (timePolynomialDerivation (E := E))

def curveCoefficientDerivation (D : Derivation ℤ E E) :
    Derivation ℤ (CurveFunctionField E) (CurveFunctionField E) :=
  extendRingDerivation (L := CurveFunctionField E) (coefficientPolynomialDerivation D)

@[simp] theorem curveTimeDerivation_coefficient (a : E) :
    curveTimeDerivation (algebraMap E (CurveFunctionField E) a) = 0 := by
  change curveTimeDerivation
    (algebraMap (Polynomial E) (CurveFunctionField E) (Polynomial.C a)) = 0
  refine (extendRingDerivation_apply (L := CurveFunctionField E)
    (timePolynomialDerivation (E := E)) (Polynomial.C a)).trans ?_
  change algebraMap (Polynomial E) (CurveFunctionField E)
    (Polynomial.derivative (Polynomial.C a)) = 0
  rw [Polynomial.derivative_C, map_zero]

@[simp] theorem curveTimeDerivation_time :
    curveTimeDerivation (curveTime (E := E)) = 1 := by
  refine (extendRingDerivation_apply (L := CurveFunctionField E)
    (timePolynomialDerivation (E := E)) Polynomial.X).trans ?_
  change algebraMap (Polynomial E) (CurveFunctionField E)
    (Polynomial.derivative Polynomial.X) = 1
  rw [Polynomial.derivative_X, map_one]

@[simp] theorem curveCoefficientDerivation_coefficient (D : Derivation ℤ E E) (a : E) :
    curveCoefficientDerivation D (algebraMap E (CurveFunctionField E) a) =
      algebraMap E (CurveFunctionField E) (D a) := by
  change curveCoefficientDerivation D
    (algebraMap (Polynomial E) (CurveFunctionField E) (Polynomial.C a)) = _
  refine (extendRingDerivation_apply (L := CurveFunctionField E)
    (coefficientPolynomialDerivation D) (Polynomial.C a)).trans ?_
  exact congrArg (algebraMap (Polynomial E) (CurveFunctionField E))
    (coefficientPolynomialDerivation_C D a)

@[simp] theorem curveCoefficientDerivation_time (D : Derivation ℤ E E) :
    curveCoefficientDerivation D (curveTime (E := E)) = 0 := by
  refine (extendRingDerivation_apply (L := CurveFunctionField E)
    (coefficientPolynomialDerivation D) Polynomial.X).trans ?_
  exact (congrArg (algebraMap (Polynomial E) (CurveFunctionField E))
    (coefficientPolynomialDerivation_X D)).trans (map_zero _)

theorem curveTime_coefficient_commute (D : Derivation ℤ E E) :
    Function.Commute curveTimeDerivation (curveCoefficientDerivation D) :=
  extendRingDerivation_commute (L := CurveFunctionField E) _ _
    (time_coefficientPolynomialDerivation_commute D)

theorem curveCoefficientDerivation_commute (D E' : Derivation ℤ E E)
    (h : Function.Commute D E') :
    Function.Commute (curveCoefficientDerivation D) (curveCoefficientDerivation E') :=
  extendRingDerivation_commute (L := CurveFunctionField E) _ _
    (coefficientPolynomialDerivation_commute D E' h)

theorem curvePolynomial_eval₂ :
    Polynomial.eval₂RingHom (algebraMap E (CurveFunctionField E)) curveTime =
      algebraMap (Polynomial E) (CurveFunctionField E) := by
  apply Polynomial.ringHom_ext
  · intro a
    change Polynomial.eval₂ (algebraMap E (CurveFunctionField E)) curveTime
      (Polynomial.C a) = _
    rw [Polynomial.eval₂_C]
    rfl
  · simp [curveTime]

end FunctionField

end HoldoutConstruction

end
end

/- Source component: CoordinateDerivationExt -/
section
/-!
Coordinate tests for derivations on a hypersurface function field and on
its finite extensions. Agreement is checked on the coefficient ring and
the actual coordinate images, then proved on every rational function.
-/

noncomputable section

namespace HoldoutConstruction

section PolynomialEvaluation

variable {R L σ : Type*} [CommRing R] [Field L]

theorem derivations_agree_eval₂
    (D E : Derivation ℤ L L) (φ : R →+* L) (x : σ → L)
    (hC : ∀ r, D (φ r) = E (φ r)) (hX : ∀ i, D (x i) = E (x i))
    (p : MvPolynomial σ R) :
    D (MvPolynomial.eval₂Hom φ x p) = E (MvPolynomial.eval₂Hom φ x p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa using hC r
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Derivation.leibniz,
      smul_eq_mul, hp, hX]

theorem derivations_agree_polynomial_eval₂
    (D E : Derivation ℤ L L) (φ : R →+* L) (x : L)
    (hC : ∀ r, D (φ r) = E (φ r)) (hX : D x = E x)
    (p : Polynomial R) :
    D (p.eval₂ φ x) = E (p.eval₂ φ x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.eval₂_monomial, Derivation.leibniz,
      Derivation.leibniz_pow, smul_eq_mul, hC, hX]

end PolynomialEvaluation

section QuotientFraction

variable {R B K L σ : Type*} [CommRing R] [CommRing B] [IsDomain B]
variable [Field K] [Algebra B K] [IsFractionRing B K] [Field L]

omit [IsDomain B] in
theorem derivations_agree_quotient_fraction
    (π : MvPolynomial σ R →+* B) (hπ : Function.Surjective π)
    (ι : K →+* L) (D E : Derivation ℤ L L)
    (hC : ∀ r, D (ι (algebraMap B K (π (MvPolynomial.C r)))) =
      E (ι (algebraMap B K (π (MvPolynomial.C r)))))
    (hX : ∀ i, D (ι (algebraMap B K (π (MvPolynomial.X i)))) =
      E (ι (algebraMap B K (π (MvPolynomial.X i))))) :
    ∀ z : K, D (ι z) = E (ι z) := by
  let ρ : MvPolynomial σ R →+* L := ι.comp ((algebraMap B K).comp π)
  have hρ : MvPolynomial.eval₂Hom (ρ.comp MvPolynomial.C)
      (fun i => ρ (MvPolynomial.X i)) = ρ := by
    ext i <;> simp
  have hpoly (p : MvPolynomial σ R) : D (ρ p) = E (ρ p) := by
    rw [← hρ]
    apply derivations_agree_eval₂
    · exact hC
    · exact hX
  have hring (a : B) : D (ι (algebraMap B K a)) = E (ι (algebraMap B K a)) := by
    obtain ⟨p, rfl⟩ := hπ a
    exact hpoly p
  intro z
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective B z
  rw [map_div₀, Derivation.leibniz_div, Derivation.leibniz_div, hring a, hring b]

omit [IsDomain B] in
theorem derivations_ext_finite_quotient_fraction [CharZero K]
    [Algebra K L] [FiniteDimensional K L]
    (π : MvPolynomial σ R →+* B) (hπ : Function.Surjective π)
    (D E : Derivation ℤ L L)
    (hC : ∀ r, D (algebraMap K L (algebraMap B K (π (MvPolynomial.C r)))) =
      E (algebraMap K L (algebraMap B K (π (MvPolynomial.C r)))))
    (hX : ∀ i, D (algebraMap K L (algebraMap B K (π (MvPolynomial.X i)))) =
      E (algebraMap K L (algebraMap B K (π (MvPolynomial.X i))))) : D = E := by
  have h := derivations_agree_quotient_fraction π hπ (algebraMap K L) D E hC hX
  have hz : D-E = 0 := by
    apply finite_derivation_unique (0 : Derivation ℤ K K)
    · intro x
      simp only [Derivation.sub_apply, h x, sub_self, Derivation.zero_apply, map_zero]
    · intro x
      simp only [Derivation.zero_apply, map_zero]
  exact sub_eq_zero.mp hz

end QuotientFraction

end HoldoutConstruction

end
end

/- Source component: DerivationEmbedding -/
section
/-!
Coordinate tests for intertwining derivations through a hypersurface
function-field embedding. The receiving field need not be finite over the
source field; only the actual coefficient and coordinate identities enter.
-/

noncomputable section

namespace HoldoutConstruction

section Polynomial

variable {R K L σ : Type*} [CommRing R] [Field K] [Field L]

theorem derivation_intertwines_polynomial
    (θ : MvPolynomial σ R →+* K) (ι : K →+* L)
    (D : Derivation ℤ K K) (E : Derivation ℤ L L)
    (hC : ∀ r, E (ι (θ (MvPolynomial.C r))) = ι (D (θ (MvPolynomial.C r))))
    (hX : ∀ i, E (ι (θ (MvPolynomial.X i))) = ι (D (θ (MvPolynomial.X i))))
    (p : MvPolynomial σ R) : E (ι (θ p)) = ι (D (θ p)) := by
  induction p using MvPolynomial.induction_on with
  | C r => exact hC r
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, hX]

end Polynomial

section QuotientFraction

variable {R B K L σ : Type*} [CommRing R] [CommRing B]
variable [Field K] [Algebra B K] [IsFractionRing B K] [Field L]

theorem derivation_intertwines_quotient_fraction
    (π : MvPolynomial σ R →+* B) (hπ : Function.Surjective π)
    (ι : K →+* L) (D : Derivation ℤ K K) (E : Derivation ℤ L L)
    (hC : ∀ r, E (ι (algebraMap B K (π (MvPolynomial.C r)))) =
      ι (D (algebraMap B K (π (MvPolynomial.C r)))) )
    (hX : ∀ i, E (ι (algebraMap B K (π (MvPolynomial.X i)))) =
      ι (D (algebraMap B K (π (MvPolynomial.X i)))) ) :
    ∀ z : K, E (ι z) = ι (D z) := by
  have hpoly := derivation_intertwines_polynomial
    ((algebraMap B K).comp π) ι D E hC hX
  have hring (a : B) : E (ι (algebraMap B K a)) = ι (D (algebraMap B K a)) := by
    obtain ⟨p,rfl⟩ := hπ a
    exact hpoly p
  intro z
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective B z
  rw [map_div₀, Derivation.leibniz_div, Derivation.leibniz_div]
  simp only [smul_eq_mul, map_mul, map_sub, map_pow, map_inv₀, hring]

end QuotientFraction

end HoldoutConstruction

end
end


