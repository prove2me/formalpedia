-- Prove2me | Definitions.Def_HodgeComputerFormal_RationalResidues
-- name    : HodgeComputerFormal_RationalResidues
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:24:16.416987+00:00
-- url     : https://prove2.me/theorems/54718777-776e-418f-acd7-d99819ae9e6e
-- title:
--   Algebraic rational-function Laurent expansions, residues, and regularity
-- statement:
--   Algebraic residue calculus for univariate rational functions $f \in \operatorname{RatFunc}(K)$ over an arbitrary field $K$:
--
--   - Formal Laurent-series expansion $\operatorname{expansion}(a) : \operatorname{RatFunc}(K) \to K(\!(t)\!)$ at $a \in K$ via shifted evaluation $X \mapsto a + t$.
--   - Finite residue $\operatorname{residue}(a, f) = [\operatorname{expansion}(a)(f)]_{t^{-1}}$, reciprocal involution $\operatorname{reciprocal}(f)(X) = f(1/X)$, and coefficient at infinity $\operatorname{infinityCoefficient}(f) = \operatorname{residue}(0, X^{-2} f(1/X))$.
--   - Regularity predicate $\operatorname{RegularAt}(a, f)$ ($\exists P, Q \in K[X],\, Q(a) \neq 0 \wedge f = P/Q$) and evaluation $\operatorname{valueAt}(a, f) = P(a)/Q(a)$, together with the vanishing lemma $\operatorname{RegularAt}(a, f) \implies \operatorname{residue}(a, f) = 0$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/RationalResidues.lean

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic

set_option autoImplicit false


/- Source component: RationalResidue. -/
section

/- Rational one-form residues for the proposed elliptic contraction.
   No certificate is asserted by these intermediate lemmas. -/
noncomputable section
open scoped LaurentSeries PowerSeries
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

local instance : Algebra (RatFunc K) (LaurentSeries K) :=
  RatFunc.liftAlgebra K (LaurentSeries K)
local instance : IsScalarTower K[X] (RatFunc K) (LaurentSeries K) :=
  RatFunc.isScalarTower_liftAlgebra K (LaurentSeries K)

def shift (a : K) : RatFunc K ≃ₐ[K] RatFunc K :=
  IsFractionRing.algEquivOfAlgEquiv (Polynomial.algEquivAevalXAddC a)

def expansion (a : K) : RatFunc K →+* LaurentSeries K :=
  (algebraMap (RatFunc K) (LaurentSeries K)).comp (shift a).toRingHom

lemma shift_polynomial (a : K) (P : K[X]) :
    shift a (algebraMap K[X] (RatFunc K) P) =
      algebraMap K[X] (RatFunc K) (P.comp (X+C a)) := by
  change IsFractionRing.algEquivOfAlgEquiv _ _ = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

lemma expansion_polynomial (a : K) (P : K[X]) :
    expansion a (algebraMap K[X] (RatFunc K) P) =
      (((P.comp (X+C a) : K[X]) : PowerSeries K) : LaurentSeries K) := by
  change algebraMap (RatFunc K) (LaurentSeries K)
    (shift a (algebraMap K[X] (RatFunc K) P)) = _
  rw [shift_polynomial]
  exact (RatFunc.coe_coe (P.comp (X+C a))).symm

lemma expansion_C (a c : K) :
    expansion a (RatFunc.C c) = HahnSeries.C c := by
  change expansion a (algebraMap K[X] (RatFunc K) (C c)) = _
  rw [expansion_polynomial]
  simp

def residue (a : K) : RatFunc K →ₗ[K] K where
  toFun f := (expansion a f).coeff (-1)
  map_add' f g := by simp
  map_smul' c f := by
    rw [RatFunc.smul_eq_C_mul, map_mul, expansion_C]
    simp [smul_eq_mul]

def uniformizer (a : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (X-C a)

lemma expansion_uniformizer (a : K) :
    expansion a (uniformizer a) = HahnSeries.single 1 1 := by
  rw [uniformizer, expansion_polynomial]
  simp

lemma residue_inverse_power (a : K) (n : ℕ) :
    residue a ((uniformizer a)^n)⁻¹ = if n=1 then 1 else 0 := by
  change (expansion a ((uniformizer a)^n)⁻¹).coeff (-1) = _
  rw [map_inv₀, map_pow, expansion_uniformizer, HahnSeries.single_pow,
    HahnSeries.inv_single]
  simp only [one_pow, inv_one, nsmul_eq_mul, mul_one, HahnSeries.coeff_single]
  have h : ((-1 : ℤ) = -(n : ℤ)) ↔ n=1 := by omega
  simp only [h]

lemma residue_polynomial (a : K) (P : K[X]) :
    residue a (algebraMap K[X] (RatFunc K) P)=0 := by
  change (expansion a (algebraMap K[X] (RatFunc K) P)).coeff (-1)=0
  rw [expansion_polynomial]
  simp [PowerSeries.coeff_coe]

lemma residue_div_polynomials (a : K) (P Q : K[X]) (hQ : Q.eval a ≠ 0) :
    residue a (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) = 0 := by
  let P0 : PowerSeries K := (P.comp (X+C a) : K[X])
  let Q0 : PowerSeries K := (Q.comp (X+C a) : K[X])
  have hq0 : PowerSeries.constantCoeff Q0 = Q.eval a := by
    simp [Q0, Polynomial.coeff_zero_eq_eval_zero]
  have hu : IsUnit Q0 := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [hq0]
    exact isUnit_iff_ne_zero.mpr hQ)
  have hqn : (Q0 : LaurentSeries K) ≠ 0 :=
    (hu.map (HahnSeries.ofPowerSeries ℤ K)).ne_zero
  obtain ⟨U, hU⟩ := hu
  have hi : (((↑(U⁻¹) : PowerSeries K)) : LaurentSeries K) =
      (Q0 : LaurentSeries K)⁻¹ := by
    apply mul_right_cancel₀ hqn
    rw [inv_mul_cancel₀ hqn, ← PowerSeries.coe_mul, ← hU]
    simp
  change (expansion a (algebraMap K[X] (RatFunc K) P /
    algebraMap K[X] (RatFunc K) Q)).coeff (-1) = 0
  rw [map_div₀, expansion_polynomial, expansion_polynomial]
  change ((P0 : LaurentSeries K)/(Q0 : LaurentSeries K)).coeff (-1)=0
  rw [div_eq_mul_inv, ← hi, ← PowerSeries.coe_mul]
  rw [PowerSeries.coeff_coe]
  norm_num

/-- A rational function is regular at `a` when it has a denominator nonzero there. -/
def RegularAt (a : K) (f : RatFunc K) : Prop :=
  ∃ P Q : K[X], Q.eval a ≠ 0 ∧
    f = algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q

lemma RegularAt.residue_eq_zero {a : K} {f : RatFunc K} (h : RegularAt a f) :
    residue a f = 0 := by
  obtain ⟨P,Q,hQ,rfl⟩ := h
  exact residue_div_polynomials a P Q hQ

lemma RegularAt.polynomial (a : K) (P : K[X]) :
    RegularAt a (algebraMap K[X] (RatFunc K) P) := by
  exact ⟨P,1,by simp,by simp⟩

lemma polynomialMap_ne_zero {P : K[X]} (hP : P ≠ 0) :
    algebraMap K[X] (RatFunc K) P ≠ 0 := by
  intro h
  apply hP
  apply IsFractionRing.injective K[X] (RatFunc K)
  simpa using h

lemma RegularAt.add {a : K} {f g : RatFunc K}
    (hf : RegularAt a f) (hg : RegularAt a g) : RegularAt a (f+g) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  obtain ⟨R,S,hS,rfl⟩ := hg
  refine ⟨P*S+R*Q,Q*S,by simpa using mul_ne_zero hQ hS,?_⟩
  have hq : algebraMap K[X] (RatFunc K) Q ≠ 0 := by
    apply polynomialMap_ne_zero
    intro h; apply hQ; simp [h]
  have hs : algebraMap K[X] (RatFunc K) S ≠ 0 := by
    apply polynomialMap_ne_zero
    intro h; apply hS; simp [h]
  simp only [map_add,map_mul]
  field_simp

lemma uniformizer_ne_zero (a : K) : uniformizer a ≠ 0 := by
  apply polynomialMap_ne_zero
  exact (monic_X_sub_C a).ne_zero

/-- Finite lists of principal terms; exponent `n` means a pole of order `n+1`. -/
def poleSum (a : K) : List (K × ℕ) → RatFunc K
  | [] => 0
  | (c,n)::terms => RatFunc.C c * ((uniformizer a)^(n+1))⁻¹ + poleSum a terms

lemma div_uniformizer_power_decomposition (a : K) (n : ℕ) (P : K[X]) :
    ∃ g : RatFunc K, ∃ terms : List (K × ℕ), RegularAt a g ∧
      algebraMap K[X] (RatFunc K) P / (uniformizer a)^n = g + poleSum a terms := by
  induction n generalizing P with
  | zero => exact ⟨_,[],RegularAt.polynomial a P,by simp [poleSum]⟩
  | succ n ih =>
    obtain ⟨g,terms,hg,he⟩ := ih (P /ₘ (X-C a))
    refine ⟨g,(P.eval a,n)::terms,hg,?_⟩
    have hp := congrArg (algebraMap K[X] (RatFunc K))
      (modByMonic_add_div P (X-C a))
    rw [modByMonic_X_sub_C_eq_C_eval] at hp
    simp only [map_add,map_mul] at hp
    change RatFunc.C (P.eval a) + uniformizer a *
      algebraMap K[X] (RatFunc K) (P /ₘ (X-C a)) =
      algebraMap K[X] (RatFunc K) P at hp
    simp only [poleSum]
    rw [add_left_comm g,← he]
    rw [← hp]
    have hu := uniformizer_ne_zero a
    field_simp
    ring

/-- Every rational function has a finite principal part at any given rational point. -/
lemma exists_regular_add_poleSum (a : K) (f : RatFunc K) :
    ∃ g : RatFunc K, ∃ terms : List (K × ℕ), RegularAt a g ∧
      f = g + poleSum a terms := by
  induction f using RatFunc.induction_on with
  | f P Q hQ =>
    obtain ⟨R,hR,hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ a
    have hr : R.eval a ≠ 0 := by
      simpa only [dvd_iff_isRoot,IsRoot] using hnd
    have hcop : IsCoprime (X-C a : K[X]) R := by
      exact ((irreducible_X_sub_C a).isCoprime_or_dvd R).resolve_right hnd
    obtain ⟨U,V,hUV⟩ := hcop.pow_left (m := Q.rootMultiplicity a)
    obtain ⟨g,terms,hg,he⟩ :=
      div_uniformizer_power_decomposition a (Q.rootMultiplicity a) (P*V)
    let r : RatFunc K := algebraMap K[X] (RatFunc K) (P*U) /
      algebraMap K[X] (RatFunc K) R
    have hreg : RegularAt a r := ⟨P*U,R,hr,rfl⟩
    refine ⟨r+g,terms,hreg.add hg,?_⟩
    rw [add_assoc,← he]
    have hR0 : algebraMap K[X] (RatFunc K) R ≠ 0 := by
      apply polynomialMap_ne_zero
      intro h; apply hr; simp [h]
    have hu := uniformizer_ne_zero a
    have huv := congrArg (algebraMap K[X] (RatFunc K)) hUV
    simp only [map_add,map_mul,map_pow,map_one] at huv
    change _ * (uniformizer a)^_ + _ * _ = 1 at huv
    conv_lhs => rw [hR,map_mul,map_pow]
    change _ / ((uniformizer a)^_ * _) = _
    dsimp [r]
    simp only [map_mul]
    field_simp [hu,hR0]
    linear_combination -(algebraMap K[X] (RatFunc K) P)*huv

lemma RegularAt.derivation {a : K} {f : RatFunc K}
    (hf : RegularAt a f) (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (hpoly : ∀ P : K[X], ∃ Q : K[X],
      D (algebraMap K[X] (RatFunc K) P) = algebraMap K[X] (RatFunc K) Q) :
    RegularAt a (D f) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  obtain ⟨P',hP'⟩ := hpoly P
  obtain ⟨Q',hQ'⟩ := hpoly Q
  refine ⟨Q*P'-P*Q',Q^2,by simpa using pow_ne_zero 2 hQ,?_⟩
  rw [D.leibniz_div,hP',hQ']
  simp only [map_sub,map_mul,map_pow,smul_eq_mul,div_eq_mul_inv]
  ring

lemma residue_term (a c : K) (n : ℕ) :
    residue a (RatFunc.C c * ((uniformizer a)^(n+1))⁻¹) =
      if n=0 then c else 0 := by
  rw [← RatFunc.smul_eq_C_mul,map_smul,residue_inverse_power]
  by_cases hn : n=0 <;> simp [hn]

lemma derivation_inverse_power (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (z : RatFunc K) (hz : z ≠ 0) (n : ℕ) :
    D ((z^(n+1))⁻¹) = -(n+1 : RatFunc K) * D z * (z^(n+2))⁻¹ := by
  rw [D.leibniz_inv,D.leibniz_pow]
  simp only [smul_eq_mul,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
  field_simp
  simp only [pow_succ]
  ring

lemma residue_derivation_term (a c k : K) (n : ℕ)
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (δ : Derivation ℤ K K)
    (hC : ∀ c, D (RatFunc.C c) = RatFunc.C (δ c))
    (hU : D (uniformizer a) = RatFunc.C k) :
    residue a (D (RatFunc.C c * ((uniformizer a)^(n+1))⁻¹)) =
      δ (residue a (RatFunc.C c * ((uniformizer a)^(n+1))⁻¹)) := by
  have he : D (RatFunc.C c * ((uniformizer a)^(n+1))⁻¹) =
      RatFunc.C (δ c) * ((uniformizer a)^(n+1))⁻¹ -
      RatFunc.C (c*(n+1)*k) * ((uniformizer a)^(n+2))⁻¹ := by
    rw [D.leibniz,derivation_inverse_power D _ (uniformizer_ne_zero a),hC,hU]
    simp only [map_mul,map_add,map_natCast,map_one,smul_eq_mul]
    ring
  rw [he,map_sub,residue_term]
  have hzero := residue_term a (c*(n+1)*k) (n+1)
  rw [show n+1+1=n+2 by omega] at hzero
  rw [hzero,if_neg (by omega : n+1 ≠ 0),sub_zero,residue_term]
  by_cases hn : n=0 <;> simp [hn]

/-- Residues commute with a base derivation even when the pole moves.
The hypothesis on the uniformizer allows its derivative to be any constant. -/
lemma residue_derivation (a k : K)
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (δ : Derivation ℤ K K)
    (hC : ∀ c, D (RatFunc.C c) = RatFunc.C (δ c))
    (hU : D (uniformizer a) = RatFunc.C k)
    (hpoly : ∀ P : K[X], ∃ Q : K[X],
      D (algebraMap K[X] (RatFunc K) P) = algebraMap K[X] (RatFunc K) Q)
    (f : RatFunc K) : residue a (D f) = δ (residue a f) := by
  obtain ⟨g,terms,hg,rfl⟩ := exists_regular_add_poleSum a f
  rw [map_add,map_add,map_add,(hg.derivation D hpoly).residue_eq_zero,
    hg.residue_eq_zero,zero_add,zero_add]
  induction terms with
  | nil => simp [poleSum]
  | cons t terms ih =>
    rcases t with ⟨c,n⟩
    simp only [poleSum,map_add]
    rw [residue_derivation_term a c k n D δ hC hU,ih]

end CrossedRationalResidue
end
end

/- Source component: RationalDerivation. -/
section

noncomputable section
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

lemma derivation_polynomial_closed
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (δ : Derivation ℤ K K) (s : K)
    (hC : ∀ c, D (RatFunc.C c) = RatFunc.C (δ c))
    (hX : D RatFunc.X = RatFunc.C s) (P : K[X]) :
    ∃ Q : K[X], D (algebraMap K[X] (RatFunc K) P) =
      algebraMap K[X] (RatFunc K) Q := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨P',hP'⟩ := hP
    obtain ⟨Q',hQ'⟩ := hQ
    exact ⟨P'+Q',by rw [map_add,map_add,hP',hQ',map_add]⟩
  | monomial n c =>
    refine ⟨C (δ c)*X^n + C (c*n*s)*X^(n-1),?_⟩
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_add,map_mul,map_pow,RatFunc.algebraMap_C,RatFunc.algebraMap_X,
      D.leibniz,D.leibniz_pow,hC,hX,smul_eq_mul,nsmul_eq_mul,map_natCast]
    ring

lemma residue_derivation_of_constants (a s : K)
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (δ : Derivation ℤ K K)
    (hC : ∀ c, D (RatFunc.C c) = RatFunc.C (δ c))
    (hX : D RatFunc.X = RatFunc.C s) (f : RatFunc K) :
    residue a (D f) = δ (residue a f) := by
  apply residue_derivation a (s-δ a) D δ hC
  · simp only [uniformizer,map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C,hX,hC]
  · exact derivation_polynomial_closed D δ s hC hX

lemma residue_exact_derivative (a : K)
    (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (hC : ∀ c, D (RatFunc.C c) = 0)
    (hX : D RatFunc.X = 1) (f : RatFunc K) : residue a (D f) = 0 := by
  have hc : ∀ c, D (RatFunc.C c) = RatFunc.C ((0 : Derivation ℤ K K) c) := by
    simpa using hC
  have hx : D RatFunc.X = RatFunc.C (1 : K) := by simpa using hX
  simpa using residue_derivation_of_constants a 1 D 0 hc hx f

end CrossedRationalResidue
end
end

/- Source component: RationalGlobalResidue. -/
section

noncomputable section
open scoped BigOperators
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

lemma transcendental_inverse_X : Transcendental K (RatFunc.X⁻¹ : RatFunc K) := by
  intro h
  exact RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)

def reciprocal : RatFunc K →ₐ[K] RatFunc K :=
  IsFractionRing.liftAlgHom (transcendental_iff_injective.mp
    (transcendental_inverse_X (K := K)))

lemma reciprocal_polynomial (P : K[X]) :
    reciprocal (algebraMap K[X] (RatFunc K) P) =
      aeval (RatFunc.X⁻¹ : RatFunc K) P := by
  exact IsFractionRing.lift_algebraMap
    (transcendental_iff_injective.mp (transcendental_inverse_X (K := K))) P

lemma reciprocal_C (c : K) : reciprocal (RatFunc.C c) = RatFunc.C c := by
  change reciprocal (algebraMap K (RatFunc K) c) = _
  exact (reciprocal (K := K)).commutes c

lemma reciprocal_X : reciprocal (RatFunc.X : RatFunc K) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X,reciprocal_polynomial]
  exact aeval_X _

lemma uniformizer_zero : uniformizer (0 : K) = RatFunc.X := by
  simp [uniformizer,RatFunc.algebraMap_X]

lemma X_ne_zero : (RatFunc.X : RatFunc K) ≠ 0 := by
  simpa only [uniformizer_zero] using uniformizer_ne_zero (0 : K)

/-- The coefficient of `X⁻¹` at infinity. Its negative is the residue at infinity. -/
def infinityCoefficient : RatFunc K →ₗ[K] K where
  toFun f := residue 0 ((RatFunc.X^2)⁻¹ * reciprocal f)
  map_add' f g := by simp [mul_add]
  map_smul' c f := by
    simp only [map_smul]
    rw [mul_smul_comm,map_smul]
    rfl

lemma infinityCoefficient_polynomial (P : K[X]) :
    infinityCoefficient (algebraMap K[X] (RatFunc K) P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,hP,hQ,add_zero]
  | monomial n c =>
    have he : (RatFunc.X^2)⁻¹ *
        reciprocal (algebraMap K[X] (RatFunc K) (monomial n c)) =
        RatFunc.C c * (RatFunc.X^(n+2))⁻¹ := by
      rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow,RatFunc.algebraMap_C,
        RatFunc.algebraMap_X,map_mul,map_pow,reciprocal_C,reciprocal_X]
      simp only [pow_add,mul_inv_rev,inv_pow]
      ring
    change residue (K := K) 0 _ = 0
    rw [he]
    have h := residue_term (0 : K) c (n+1)
    rw [show n+1+1=n+2 by omega] at h
    simpa only [uniformizer_zero,if_neg (by omega : n+1 ≠ 0)] using h

lemma reciprocal_uniformizer (a : K) :
    reciprocal (uniformizer a) =
      (1-RatFunc.C a*RatFunc.X)/RatFunc.X := by
  simp only [uniformizer,map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C,
    reciprocal_X,reciprocal_C]
  field_simp [X_ne_zero]

lemma one_sub_C_mul_X_ne_zero (a : K) :
    (1-RatFunc.C a*RatFunc.X : RatFunc K) ≠ 0 := by
  have hp : (1-C a*X : K[X]).eval 0 ≠ 0 := by simp
  have : (1-C a*X : K[X]) ≠ 0 := by intro h; simp [h] at hp
  simpa using polynomialMap_ne_zero this

lemma infinityCoefficient_term (a c : K) (n : ℕ) :
    infinityCoefficient (RatFunc.C c*((uniformizer a)^(n+1))⁻¹) =
      if n=0 then c else 0 := by
  cases n with
  | zero =>
    have he : (RatFunc.X^2)⁻¹ *
        reciprocal (RatFunc.C c*((uniformizer a)^(0+1))⁻¹) =
        RatFunc.C c*(RatFunc.X)⁻¹ +
        RatFunc.C (c*a)/(1-RatFunc.C a*RatFunc.X) := by
      simp only [map_mul,map_inv₀,map_pow,reciprocal_C,reciprocal_uniformizer]
      simp only [div_pow,inv_div]
      have hL : (1-RatFunc.X*RatFunc.C a : RatFunc K) ≠ 0 := by
        simpa only [mul_comm] using one_sub_C_mul_X_ne_zero a
      field_simp [X_ne_zero,one_sub_C_mul_X_ne_zero,hL]
      ring
    change residue (K := K) 0 _ = _
    rw [he,map_add]
    have hr : RegularAt (0 : K)
        (RatFunc.C (c*a)/(1-RatFunc.C a*RatFunc.X)) := by
      exact ⟨C (c*a),1-C a*X,by simp,by simp⟩
    rw [hr.residue_eq_zero,add_zero]
    simpa only [uniformizer_zero,zero_add,pow_one,if_pos rfl] using residue_term (0 : K) c 0
  | succ n =>
    have he : (RatFunc.X^2)⁻¹ *
        reciprocal (RatFunc.C c*((uniformizer a)^(n+1+1))⁻¹) =
        algebraMap K[X] (RatFunc K) (C c*X^n) /
        algebraMap K[X] (RatFunc K) ((1-C a*X)^(n+2)) := by
      simp only [map_mul,map_pow,map_sub,map_one,RatFunc.algebraMap_C,
        RatFunc.algebraMap_X,map_inv₀,reciprocal_C,reciprocal_uniformizer]
      rw [show n+1+1=n+2 by omega]
      simp only [div_pow,inv_div]
      field_simp [X_ne_zero,one_sub_C_mul_X_ne_zero]
      simp only [pow_succ]
      ring
    change residue (K := K) 0 _ = _
    rw [he,residue_div_polynomials (hQ := by simp)]
    simp

end CrossedRationalResidue
end
end

/- Source component: RationalLocalValue. -/
section

noncomputable section
open scoped LaurentSeries PowerSeries
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra (RatFunc K) (LaurentSeries K) :=
  RatFunc.liftAlgebra K (LaurentSeries K)
local instance : IsScalarTower K[X] (RatFunc K) (LaurentSeries K) :=
  RatFunc.isScalarTower_liftAlgebra K (LaurentSeries K)

def valueAt (a : K) : RatFunc K →ₗ[K] K where
  toFun f := (expansion a f).coeff 0
  map_add' f g := by simp
  map_smul' c f := by
    rw [RatFunc.smul_eq_C_mul,map_mul,expansion_C]
    simp [smul_eq_mul]

lemma valueAt_div_polynomials (a : K) (P Q : K[X]) (hQ : Q.eval a ≠ 0) :
    valueAt a (algebraMap K[X] (RatFunc K) P /
      algebraMap K[X] (RatFunc K) Q) = P.eval a / Q.eval a := by
  let P0 : PowerSeries K := (P.comp (X+C a) : K[X])
  let Q0 : PowerSeries K := (Q.comp (X+C a) : K[X])
  have hp0 : PowerSeries.constantCoeff P0 = P.eval a := by
    simp [P0,Polynomial.coeff_zero_eq_eval_zero]
  have hq0 : PowerSeries.constantCoeff Q0 = Q.eval a := by
    simp [Q0,Polynomial.coeff_zero_eq_eval_zero]
  have hu : IsUnit Q0 := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    rw [hq0]
    exact isUnit_iff_ne_zero.mpr hQ)
  have hqn : (Q0 : LaurentSeries K) ≠ 0 :=
    (hu.map (HahnSeries.ofPowerSeries ℤ K)).ne_zero
  obtain ⟨U,hU⟩ := hu
  have hi : (((↑(U⁻¹) : PowerSeries K)) : LaurentSeries K) =
      (Q0 : LaurentSeries K)⁻¹ := by
    apply mul_right_cancel₀ hqn
    rw [inv_mul_cancel₀ hqn,← PowerSeries.coe_mul,← hU]
    simp
  have hic : PowerSeries.constantCoeff (↑(U⁻¹) : PowerSeries K) = (Q.eval a)⁻¹ := by
    apply mul_right_cancel₀ hQ
    rw [inv_mul_cancel₀ hQ,← hq0,← map_mul,← hU]
    simp
  change (expansion a (algebraMap K[X] (RatFunc K) P /
    algebraMap K[X] (RatFunc K) Q)).coeff 0 = _
  rw [map_div₀,expansion_polynomial,expansion_polynomial]
  change ((P0 : LaurentSeries K)/(Q0 : LaurentSeries K)).coeff 0 = _
  rw [div_eq_mul_inv,← hi,← PowerSeries.coe_mul,PowerSeries.coeff_coe]
  norm_num only
  simp only [ite_false]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [map_mul,hp0,hic,div_eq_mul_inv]

lemma residue_div_uniformizer (a : K) (f : RatFunc K) :
    residue a (f/uniformizer a) = valueAt a f := by
  change (expansion a (f/uniformizer a)).coeff (-1) = (expansion a f).coeff 0
  rw [map_div₀,expansion_uniformizer,div_eq_mul_inv,HahnSeries.inv_single,
    HahnSeries.coeff_mul_single]
  simp

lemma residue_div_uniformizer_sq (a : K) (D : Derivation ℤ (RatFunc K) (RatFunc K))
    (hC : ∀ c, D (RatFunc.C c) = 0) (hX : D RatFunc.X = 1) (f : RatFunc K) :
    residue a (f/(uniformizer a)^2) = valueAt a (D f) := by
  have hu : D (uniformizer a) = 1 := by
    simp only [uniformizer,map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C,hX,hC,sub_zero]
  have he : D (f/uniformizer a) = D f/uniformizer a-f/(uniformizer a)^2 := by
    rw [D.leibniz_div,hu]
    simp only [smul_eq_mul,mul_one]
    field_simp [uniformizer_ne_zero a]
  have hr := residue_exact_derivative a D hC hX (f/uniformizer a)
  rw [he,map_sub,residue_div_uniformizer] at hr
  exact (sub_eq_zero.mp hr).symm

end CrossedRationalResidue
end
end


