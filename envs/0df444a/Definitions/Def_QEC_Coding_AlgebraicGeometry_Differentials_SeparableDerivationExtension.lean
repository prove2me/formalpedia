-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
-- name    : QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:16:04.116196+00:00
-- url     : https://prove2.me/theorems/6f6fc1bf-9134-4be0-ba5c-661e3f32a993
-- title:
--   Separable Derivation Extension
-- statement:
--   Definitions and structural lemmas for Separable Derivation Extension, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/SeparableDerivationExtension.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Polynomial.Module.AEval
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
namespace SeparableDerivationExtension
open scoped RatFunc
variable {k F M : Type*} [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
variable [AddCommGroup M] [Module k M] [Module (RatFunc k) M] [Module F M]
variable [IsScalarTower k F M] [IsScalarTower (RatFunc k) F M] [IsScalarTower k (RatFunc k) M]
noncomputable def coefficientDerivationSum (D : Derivation k F M) (q : Polynomial (RatFunc k))
    (y : F) : M :=
  q.sum fun n a => y ^ n • D (algebraMap (RatFunc k) F a)
theorem coefficientDerivationSum_monomial (D : Derivation k F M) (n : ℕ) (a : RatFunc k) (y : F) :
    coefficientDerivationSum D (Polynomial.monomial n a) y
      = y ^ n • D (algebraMap (RatFunc k) F a) := by
  change (Polynomial.monomial n a).sum (fun n' c => y ^ n' • D (algebraMap (RatFunc k) F c))
    = y ^ n • D (algebraMap (RatFunc k) F a)
  rw [Polynomial.sum_monomial_index]
  simp
theorem coefficientDerivationSum_add (D : Derivation k F M) (p q : Polynomial (RatFunc k)) (y : F) :
    coefficientDerivationSum D (p + q) y = coefficientDerivationSum D p y
      + coefficientDerivationSum D q y := by
  change (p + q).sum (fun n' c => y ^ n' • D (algebraMap (RatFunc k) F c))
    = p.sum (fun n' c => y ^ n' • D (algebraMap (RatFunc k) F c))
      + q.sum (fun n' c => y ^ n' • D (algebraMap (RatFunc k) F c))
  rw [Polynomial.sum_add_index (f := fun n' c => y ^ n' • D (algebraMap (RatFunc k) F c))
    (hf := by intro i; simp)
    (h_add := by intro a b₁ b₂; simp only [map_add, smul_add])]
theorem map_aeval_of_coeffs (D : Derivation k F M) (q : Polynomial (RatFunc k)) (y : F) :
    D (Polynomial.aeval y q) = Polynomial.aeval y q.derivative • D y
      + coefficientDerivationSum D q y := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.aeval_add, D.map_add, Polynomial.derivative_add, Polynomial.aeval_add,
        add_smul, hp, hq, coefficientDerivationSum_add]
      abel_nf
  | monomial n a =>
      rw [show Polynomial.monomial n a = Polynomial.C a * Polynomial.X ^ n from
        (Polynomial.C_mul_X_pow_eq_monomial : Polynomial.C a * Polynomial.X ^ n = Polynomial.monomial n a).symm]
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [D.leibniz (algebraMap (RatFunc k) F a) (y ^ n)]
      rw [D.leibniz_pow]
      rw [show Polynomial.derivative (Polynomial.C a * Polynomial.X ^ n)
          = Polynomial.C a * (Polynomial.C (n : RatFunc k) * Polynomial.X ^ (n - 1)) by
        rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
          Polynomial.derivative_X_pow]]
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_mul, Polynomial.aeval_C,
        map_pow, Polynomial.aeval_X]
      rw [show coefficientDerivationSum D (Polynomial.C a * Polynomial.X ^ n) y
          = coefficientDerivationSum D (Polynomial.monomial n a) y by
        rw [Polynomial.C_mul_X_pow_eq_monomial]]
      rw [coefficientDerivationSum_monomial]
      rw [← Nat.cast_smul_eq_nsmul (R := F)]
      simp only [smul_smul, mul_assoc, map_natCast]
theorem extension_unique {D₁ D₂ : Derivation k F M}
    (h : D₁.compAlgebraMap (RatFunc k) = D₂.compAlgebraMap (RatFunc k)) : D₁ = D₂ := by
  refine Derivation.ext ?_
  intro x
  let p : Polynomial (RatFunc k) := minpoly (RatFunc k) x
  have hx : Polynomial.aeval x p = 0 := minpoly.aeval (RatFunc k) x
  have hD₁ := map_aeval_of_coeffs D₁ p x
  have hD₂ := map_aeval_of_coeffs D₂ p x
  rw [hx, D₁.map_zero] at hD₁
  rw [hx, D₂.map_zero] at hD₂
  have hcoeff : coefficientDerivationSum D₁ p x = coefficientDerivationSum D₂ p x := by
    dsimp only [coefficientDerivationSum, Polynomial.sum]
    apply Finset.sum_congr
    · rfl
    · intro n hn
      have := Derivation.congr_fun h (p.coeff n)
      simpa [Derivation.compAlgebraMap_apply] using congrArg (fun m => x ^ n • m) this
  have hunit : Polynomial.aeval x p.derivative ≠ 0 :=
    Polynomial.Separable.aeval_derivative_ne_zero
      (Algebra.IsSeparable.isSeparable' x) hx
  have hunit' : IsUnit (Polynomial.aeval x p.derivative) := hunit.isUnit
  have hmain : Polynomial.aeval x p.derivative • D₁ x = Polynomial.aeval x p.derivative • D₂ x := by
    have hA : Polynomial.aeval x p.derivative • D₁ x = -coefficientDerivationSum D₁ p x := by
      simpa [eq_neg_iff_add_eq_zero] using hD₁.symm
    have hB : Polynomial.aeval x p.derivative • D₂ x = -coefficientDerivationSum D₂ p x := by
      simpa [eq_neg_iff_add_eq_zero] using hD₂.symm
    rw [hA, hB, hcoeff]
  exact hunit'.smul_left_cancel.mp hmain
noncomputable def polynomialExtensionValue (D : Derivation k (RatFunc k) M) (y : F)
    (v : M) (q : Polynomial (RatFunc k)) : M :=
  q.sum (fun n a => y ^ n • D a) + Polynomial.aeval y q.derivative • v
theorem polynomialExtensionValue_add (D : Derivation k (RatFunc k) M) (y : F) (v : M)
    (p q : Polynomial (RatFunc k)) :
    polynomialExtensionValue D y v (p + q) = polynomialExtensionValue D y v p
      + polynomialExtensionValue D y v q := by
  change (p + q).sum (fun n a => y ^ n • D a) + Polynomial.aeval y (p + q).derivative • v
    = p.sum (fun n a => y ^ n • D a) + Polynomial.aeval y p.derivative • v
      + (q.sum (fun n a => y ^ n • D a) + Polynomial.aeval y q.derivative • v)
  rw [Polynomial.sum_add_index (f := fun n a => y ^ n • D a)
      (hf := by intro i; simp)
      (h_add := by intro a b₁ b₂; simp only [map_add, smul_add]),
    Polynomial.derivative_add, Polynomial.aeval_add, add_smul]
  abel_nf
theorem polynomialExtensionValue_C (D : Derivation k (RatFunc k) M) (y : F) (v : M)
    (a : RatFunc k) :
    polynomialExtensionValue D y v (Polynomial.C a) = D a := by
  change (Polynomial.C a).sum (fun n c => y ^ n • D c) + Polynomial.aeval y (Polynomial.C a).derivative • v = D a
  rw [Polynomial.sum_C_index, Polynomial.derivative_C]
  · simp
  · simp
theorem sum_sum_eq {S : Type*} [AddCommMonoid S] {ι : Type*} (rs : Finset ι)
    (ps : ι → Polynomial (RatFunc k)) (f : ℕ → RatFunc k → S)
    (hf : ∀ i, f i 0 = 0) (hadd : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
    (∑ i ∈ rs, ps i).sum f = ∑ i ∈ rs, (ps i).sum f := by
  classical
  induction rs using Finset.induction_on with
  | empty => simp
  | insert i rs' hi ih =>
      rw [Finset.sum_insert hi, Polynomial.sum_add_index _ _ f hf hadd, ih, Finset.sum_insert hi]
theorem aeval_eq_sum (y : F) (r : Polynomial (RatFunc k)) :
    Polynomial.aeval y r = r.sum (fun j b => algebraMap (RatFunc k) F b • y ^ j) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.aeval_add,
        Polynomial.sum_add_index (f := fun j b => algebraMap (RatFunc k) F b • y ^ j)
          (hf := by intro i; simp)
          (h_add := by intro a b₁ b₂; simp only [map_add, add_smul]),
        hp, hq]
  | monomial n a =>
      rw [show (Polynomial.monomial n a).sum (fun j b => algebraMap (RatFunc k) F b • y ^ j)
          = algebraMap (RatFunc k) F a * y ^ n by
        rw [Polynomial.sum_monomial_index (f := fun j b => algebraMap (RatFunc k) F b • y ^ j)
          (hf := by simp)]
        simp]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
theorem shuffle_left (D : Derivation k (RatFunc k) M) (y : F) (n : ℕ) (a : RatFunc k)
    (j : ℕ) (b : RatFunc k) :
    y ^ (n + j) • (a • D b) = Polynomial.aeval y (Polynomial.monomial n a) • (y ^ j • D b) := by
  rw [← algebraMap_smul (R := RatFunc k) (A := F)]
  rw [pow_add, smul_smul, smul_smul]
  exact congrArg (fun s => s • D b) (by
    rw [show Polynomial.aeval y (Polynomial.monomial n a) = algebraMap (RatFunc k) F a * y ^ n by
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      rw [Polynomial.aeval_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]]
    ring)
theorem shuffle_right (D : Derivation k (RatFunc k) M) (y : F) (n : ℕ) (a : RatFunc k)
    (j : ℕ) (b : RatFunc k) :
    y ^ (n + j) • (b • D a) = (algebraMap (RatFunc k) F b * y ^ j) • (y ^ n • D a) := by
  rw [← algebraMap_smul (R := RatFunc k) (A := F)]
  rw [pow_add, smul_smul, smul_smul]
  exact congrArg (fun s => s • D a) (by ring)
theorem coefficientSum_monomial_mul (D : Derivation k (RatFunc k) M) (y : F) (n : ℕ)
    (a : RatFunc k) (r : Polynomial (RatFunc k)) :
    (r.sum fun j b => Polynomial.monomial (n + j) (a * b)).sum (fun n' c => y ^ n' • D c)
      = Polynomial.aeval y (Polynomial.monomial n a) • (r.sum fun j b => y ^ j • D b)
        + Polynomial.aeval y r • (y ^ n • D a) := by
  have hsum1 : (r.sum fun j b => Polynomial.monomial (n + j) (a * b)).sum (fun n' c => y ^ n' • D c)
      = ∑ j ∈ r.support, (Polynomial.monomial (n + j) (a * r.coeff j)).sum (fun n' c => y ^ n' • D c) := by
    rw [show (r.sum fun j b => Polynomial.monomial (n + j) (a * b))
        = ∑ j ∈ r.support, Polynomial.monomial (n + j) (a * r.coeff j) by
      rfl]
    exact sum_sum_eq (rs := r.support) (ps := fun j => Polynomial.monomial (n + j) (a * r.coeff j))
      (f := fun n' c => y ^ n' • D c) (hf := by intro i; simp)
      (hadd := by intro n' b₁ b₂; simp only [map_add, smul_add])
  rw [hsum1]
  have hmonomial :
      (∑ j ∈ r.support, (Polynomial.monomial (n + j) (a * r.coeff j)).sum
        (fun n' c => y ^ n' • D c)) = r.sum (fun j b => y ^ (n + j) • D (a * b)) := by
    change (∑ j ∈ r.support, (Polynomial.monomial (n + j) (a * r.coeff j)).sum
      (fun n' c => y ^ n' • D c)) = ∑ j ∈ r.support, y ^ (n + j) • D (a * r.coeff j)
    apply Finset.sum_congr
    · rfl
    · intro j hj
      exact Polynomial.sum_monomial_index (n := n + j) (a := a * r.coeff j)
        (f := fun n' c => y ^ n' • D c) (hf := by simp)
  rw [hmonomial]
  have hleib : (r.sum fun j b => y ^ (n + j) • D (a * b))
      = (r.sum fun j b => y ^ (n + j) • (a • D b) + y ^ (n + j) • (b • D a)) := by
    dsimp only [Polynomial.sum]
    apply Finset.sum_congr
    · rfl
    · intro j hj
      rw [D.leibniz a (r.coeff j), smul_add]
  rw [hleib]
  rw [Polynomial.sum_add]
  have hsum2 : (r.sum fun j b => y ^ (n + j) • (a • D b))
      = Polynomial.aeval y (Polynomial.monomial n a) • (r.sum fun j b => y ^ j • D b) := by
    rw [Polynomial.smul_sum]
    dsimp only [Polynomial.sum]
    apply Finset.sum_congr
    · rfl
    · intro j hj
      exact shuffle_left D y n a j (r.coeff j)
  rw [hsum2]
  have hsum3 : (r.sum fun j b => y ^ (n + j) • (b • D a))
      = Polynomial.aeval y r • (y ^ n • D a) := by
    rw [show Polynomial.aeval y r • (y ^ n • D a)
        = (r.sum fun j b => (algebraMap (RatFunc k) F b • y ^ j) • (y ^ n • D a)) by
      rw [aeval_eq_sum y r]
      dsimp only [Polynomial.sum]
      rw [Finset.sum_smul]]
    rw [show (r.sum fun j b => y ^ (n + j) • (b • D a))
        = (r.sum fun j b => (algebraMap (RatFunc k) F b • y ^ j) • (y ^ n • D a)) by
      dsimp only [Polynomial.sum]
      apply Finset.sum_congr
      · rfl
      · intro j hj
        exact shuffle_right D y n a j (r.coeff j)]
  rw [hsum3]
theorem polynomialExtensionValue_leibniz (D : Derivation k (RatFunc k) M) (y : F) (v : M)
    (q r : Polynomial (RatFunc k)) :
    polynomialExtensionValue D y v (q * r) = Polynomial.aeval y q • polynomialExtensionValue D y v r
      + Polynomial.aeval y r • polynomialExtensionValue D y v q := by
  induction q using Polynomial.induction_on' with
  | add q₁ q₂ hq₁ hq₂ =>
      rw [add_mul, polynomialExtensionValue_add, hq₁, hq₂, Polynomial.aeval_add, add_smul]
      rw [polynomialExtensionValue_add, smul_add]
      abel_nf
  | monomial n a =>
      by_cases ha : a = 0
      · subst ha
        simp [polynomialExtensionValue]
      · rw [← Polynomial.C_mul_X_pow_eq_monomial]
        change (Polynomial.C a * Polynomial.X ^ n * r).sum (fun n' c => y ^ n' • D c)
            + Polynomial.aeval y (Polynomial.C a * Polynomial.X ^ n * r).derivative • v
          = Polynomial.aeval y (Polynomial.C a * Polynomial.X ^ n) •
              (r.sum (fun j b => y ^ j • D b) + Polynomial.aeval y r.derivative • v)
            + Polynomial.aeval y r •
              ((Polynomial.C a * Polynomial.X ^ n).sum (fun n' c => y ^ n' • D c)
                + Polynomial.aeval y (Polynomial.C a * Polynomial.X ^ n).derivative • v)
        rw [show Polynomial.derivative (Polynomial.C a * Polynomial.X ^ n * r)
            = Polynomial.C a * (Polynomial.C (n : RatFunc k) * Polynomial.X ^ (n - 1)) * r
              + Polynomial.C a * Polynomial.X ^ n * Polynomial.derivative r by
          rw [Polynomial.derivative_mul]
          rw [show Polynomial.derivative (Polynomial.C a * Polynomial.X ^ n)
              = Polynomial.C a * (Polynomial.C (n : RatFunc k) * Polynomial.X ^ (n - 1)) by
            rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
              Polynomial.derivative_X_pow]]]
        rw [show Polynomial.C a * Polynomial.X ^ n * r
            = r.sum (fun j b => Polynomial.monomial (n + j) (a * b)) by
          rw [show Polynomial.C a * Polynomial.X ^ n = Polynomial.monomial n a from
            (Polynomial.C_mul_X_pow_eq_monomial : Polynomial.C a * Polynomial.X ^ n = Polynomial.monomial n a)]
          rw [Polynomial.mul_eq_sum_sum, Polynomial.support_monomial n ha]
          simp]
        rw [coefficientSum_monomial_mul D y n a r]
        have hmonomial_sum :
            ((Polynomial.C a * Polynomial.X ^ n : Polynomial (RatFunc k)).sum
              (fun n' c => y ^ n' • D c)) = y ^ n • D a := by
          rw [Polynomial.C_mul_X_pow_eq_monomial]
          exact Polynomial.sum_monomial_index (n := n) (a := a)
            (f := fun n' c => y ^ n' • D c) (hf := by simp)
        rw [hmonomial_sum]
        rw [show Polynomial.derivative (Polynomial.C a * Polynomial.X ^ n)
            = Polynomial.C a * (Polynomial.C (n : RatFunc k) * Polynomial.X ^ (n - 1)) by
          rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
            Polynomial.derivative_X_pow]]
        rw [show Polynomial.aeval y (Polynomial.monomial n a) = algebraMap (RatFunc k) F a * y ^ n by
          rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.aeval_mul, Polynomial.aeval_C,
            map_pow, Polynomial.aeval_X]]
        rw [show Polynomial.aeval y (Polynomial.C a * Polynomial.X ^ n)
            = algebraMap (RatFunc k) F a * y ^ n by
          rw [Polynomial.aeval_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]]
        rw [show Polynomial.aeval y (Polynomial.C a * (Polynomial.C (n : RatFunc k) * Polynomial.X ^ (n - 1)))
            = algebraMap (RatFunc k) F a * algebraMap (RatFunc k) F (n : RatFunc k) * y ^ (n - 1) by
          rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_mul, Polynomial.aeval_C, map_pow,
            Polynomial.aeval_X]
          ring]
        rw [Polynomial.aeval_add]
        rw [show Polynomial.aeval y (Polynomial.C a * (Polynomial.C (n : RatFunc k) * Polynomial.X ^ (n - 1)) * r)
            = algebraMap (RatFunc k) F a * algebraMap (RatFunc k) F (n : RatFunc k) * y ^ (n - 1) * Polynomial.aeval y r by
          rw [Polynomial.aeval_mul, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_mul, Polynomial.aeval_C,
            map_pow, Polynomial.aeval_X]
          ring]
        rw [show Polynomial.aeval y (Polynomial.C a * Polynomial.X ^ n * Polynomial.derivative r)
            = algebraMap (RatFunc k) F a * y ^ n * Polynomial.aeval y r.derivative by
          rw [Polynomial.aeval_mul, Polynomial.aeval_mul, Polynomial.aeval_C, map_pow,
            Polynomial.aeval_X]]
        rw [show algebraMap (RatFunc k) F a * algebraMap (RatFunc k) F (n : RatFunc k) * y ^ (n - 1) * Polynomial.aeval y r
            = Polynomial.aeval y r * (algebraMap (RatFunc k) F a * algebraMap (RatFunc k) F (n : RatFunc k) * y ^ (n - 1)) by
          ring]
        rw [show algebraMap (RatFunc k) F a * y ^ n * Polynomial.aeval y r.derivative
            = Polynomial.aeval y r.derivative * (algebraMap (RatFunc k) F a * y ^ n) by
          ring]
        simp only [smul_add, add_smul, mul_smul]
        simp only [smul_smul]
        rw [show Polynomial.aeval y r.derivative * (algebraMap (RatFunc k) F a * y ^ n)
            = algebraMap (RatFunc k) F a * (y ^ n * Polynomial.aeval y r.derivative) by ring] <;> abel_nf
local instance moduleKAEval (y : F) : Module k (Module.AEval (RatFunc k) M y) :=
  inferInstanceAs (Module k M)
noncomputable def polynomialExtensionDerivation (D : Derivation k (RatFunc k) M) (y : F)
    (v : M) : Derivation k (Polynomial (RatFunc k)) (Module.AEval (RatFunc k) M y) := by
  exact {
    toFun q := Module.AEval.of (RatFunc k) M y (polynomialExtensionValue D y v q)
    map_add' p q := by
      change polynomialExtensionValue D y v (p + q) = polynomialExtensionValue D y v p
        + polynomialExtensionValue D y v q
      exact polynomialExtensionValue_add D y v p q
    map_smul' c q := by
      change polynomialExtensionValue D y v (c • q) = c • polynomialExtensionValue D y v q
      rw [show c • q = (algebraMap k (RatFunc k) c) • q by rw [algebraMap_smul],
        Polynomial.smul_eq_C_mul, polynomialExtensionValue_leibniz, polynomialExtensionValue_C]
      simp only [Polynomial.aeval_C, D.map_algebraMap, smul_zero, add_zero,
        IsScalarTower.algebraMap_apply, algebraMap_smul]
    map_one_eq_zero' := by
      change polynomialExtensionValue D y v (Polynomial.C 1) = 0
      rw [polynomialExtensionValue_C, D.map_one_eq_zero]
    leibniz' p q := by
      change polynomialExtensionValue D y v (p * q) = Polynomial.aeval y p •
        polynomialExtensionValue D y v q + Polynomial.aeval y q • polynomialExtensionValue D y v p
      exact polynomialExtensionValue_leibniz D y v p q
  }
theorem polynomialExtensionDerivation_C (D : Derivation k (RatFunc k) M) (y : F) (v : M)
    (a : RatFunc k) :
    polynomialExtensionDerivation D y v (Polynomial.C a) = Module.AEval.of (RatFunc k) M y (D a) := by
  change Module.AEval.of (RatFunc k) M y
    (polynomialExtensionValue D y v (Polynomial.C a)) = Module.AEval.of (RatFunc k) M y (D a)
  rw [polynomialExtensionValue_C]
noncomputable def descendPolynomialDerivation (y : F)
    (D : Derivation k (Polynomial (RatFunc k)) (Module.AEval (RatFunc k) M y))
    (hsurj : Function.Surjective (fun q : Polynomial (RatFunc k) => Polynomial.aeval y q))
    (hker : ∀ q : Polynomial (RatFunc k), Polynomial.aeval y q = 0 → D q = 0) :
    Derivation k F M := by
  let s : F → Polynomial (RatFunc k) := Function.surjInv hsurj
  have hs (x : F) : Polynomial.aeval y (s x) = x := Function.surjInv_eq hsurj x
  have hD_add (x z : F) : D (s (x + z)) = D (s x) + D (s z) := by
    have hzero : Polynomial.aeval y (s (x + z) - (s x + s z)) = 0 := by
      simp only [map_sub, map_add, hs, sub_self]
    have hDzero := hker _ hzero
    have hD_eq : D (s (x + z)) = D (s x + s z) := by
      simpa only [map_sub, sub_eq_zero] using hDzero
    calc
      D (s (x + z)) = D (s x + s z) := hD_eq
      _ = D (s x) + D (s z) := D.map_add _ _
  have hD_smul (c : k) (x : F) : D (s (c • x)) = c • D (s x) := by
    have hzero : Polynomial.aeval y (s (c • x) - c • s x) = 0 := by
      rw [map_sub, hs,
        show c • s x = Polynomial.C (algebraMap k (RatFunc k) c) * s x by
          rw [← algebraMap_smul (R := k) (A := RatFunc k), Polynomial.smul_eq_C_mul],
        Polynomial.aeval_mul, Polynomial.aeval_C, hs]
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k (RatFunc k) F, sub_self]
    have hDzero := hker _ hzero
    have hD_eq : D (s (c • x)) = D (c • s x) := by
      exact sub_eq_zero.mp (by simpa only [map_sub] using hDzero)
    calc
      D (s (c • x)) = D (c • s x) := hD_eq
      _ = c • D (s x) := D.map_smul c (s x)
  have hD_one : D (s (1 : F)) = 0 := by
    have hzero : Polynomial.aeval y (s (1 : F) - 1) = 0 := by
      rw [map_sub, hs, map_one, sub_self]
    have hDzero := hker _ hzero
    have hD_eq : D (s (1 : F)) = D 1 := by
      exact sub_eq_zero.mp (by simpa only [map_sub] using hDzero)
    simpa only [D.map_one_eq_zero] using hD_eq
  have hD_mul (x z : F) :
      D (s (x * z)) = s x • D (s z) + s z • D (s x) := by
    have hzero : Polynomial.aeval y (s (x * z) - s x * s z) = 0 := by
      simp only [map_sub, map_mul, hs, sub_self]
    have hDzero := hker _ hzero
    have hD_eq : D (s (x * z)) = D (s x * s z) := by
      simpa only [map_sub, sub_eq_zero] using hDzero
    calc
      D (s (x * z)) = D (s x * s z) := hD_eq
      _ = s x • D (s z) + s z • D (s x) := D.leibniz _ _
  exact {
    toFun x := (Module.AEval.of (RatFunc k) M y).symm (D (s x))
    map_add' x z := by
      calc
        (Module.AEval.of (RatFunc k) M y).symm (D (s (x + z)))
            = (Module.AEval.of (RatFunc k) M y).symm (D (s x) + D (s z)) :=
              congrArg (Module.AEval.of (RatFunc k) M y).symm (hD_add x z)
        _ = (Module.AEval.of (RatFunc k) M y).symm (D (s x))
            + (Module.AEval.of (RatFunc k) M y).symm (D (s z)) := by rw [map_add]
    map_smul' c x := by
      calc
        (Module.AEval.of (RatFunc k) M y).symm (D (s (c • x)))
            = (Module.AEval.of (RatFunc k) M y).symm (c • D (s x)) :=
              congrArg (Module.AEval.of (RatFunc k) M y).symm (hD_smul c x)
        _ = c • (Module.AEval.of (RatFunc k) M y).symm (D (s x)) := rfl
    map_one_eq_zero' := by
      calc
        (Module.AEval.of (RatFunc k) M y).symm (D (s (1 : F)))
            = (Module.AEval.of (RatFunc k) M y).symm 0 :=
              congrArg (Module.AEval.of (RatFunc k) M y).symm hD_one
        _ = 0 := by simp
    leibniz' x z := by
      calc
        (Module.AEval.of (RatFunc k) M y).symm (D (s (x * z)))
            = (Module.AEval.of (RatFunc k) M y).symm
                (s x • D (s z) + s z • D (s x)) :=
              congrArg (Module.AEval.of (RatFunc k) M y).symm (hD_mul x z)
        _ = (Module.AEval.of (RatFunc k) M y).symm (s x • D (s z))
            + (Module.AEval.of (RatFunc k) M y).symm (s z • D (s x)) := by rw [map_add]
        _ = x • (Module.AEval.of (RatFunc k) M y).symm (D (s z))
            + z • (Module.AEval.of (RatFunc k) M y).symm (D (s x)) := by
              rw [Module.AEval.of_symm_smul, Module.AEval.of_symm_smul, hs, hs]
  }
theorem descendPolynomialDerivation_apply_aeval (y : F)
    (D : Derivation k (Polynomial (RatFunc k)) (Module.AEval (RatFunc k) M y))
    (hsurj : Function.Surjective (fun q : Polynomial (RatFunc k) => Polynomial.aeval y q))
    (hker : ∀ q : Polynomial (RatFunc k), Polynomial.aeval y q = 0 → D q = 0)
    (q : Polynomial (RatFunc k)) :
    descendPolynomialDerivation y D hsurj hker (Polynomial.aeval y q)
      = (Module.AEval.of (RatFunc k) M y).symm (D q) := by
  change (Module.AEval.of (RatFunc k) M y).symm
      (D (Function.surjInv hsurj (Polynomial.aeval y q)))
    = (Module.AEval.of (RatFunc k) M y).symm (D q)
  have hzero : Polynomial.aeval y (Function.surjInv hsurj (Polynomial.aeval y q) - q) = 0 := by
    rw [map_sub, Function.surjInv_eq hsurj, sub_self]
  have hDzero := hker _ hzero
  have hD_eq : D (Function.surjInv hsurj (Polynomial.aeval y q)) = D q := by
    exact sub_eq_zero.mp (by simpa only [map_sub] using hDzero)
  exact congrArg (Module.AEval.of (RatFunc k) M y).symm hD_eq
noncomputable def separableGenerator : F :=
  (Field.powerBasisOfFiniteOfSeparable (RatFunc k) F).gen
noncomputable def separableGeneratorMinpoly : Polynomial (RatFunc k) :=
  minpoly (RatFunc k) (separableGenerator (k := k) (F := F))
local notation3 "η" => separableGenerator (k := k) (F := F)
local notation3 "μ" => separableGeneratorMinpoly (k := k) (F := F)
theorem separableGenerator_aeval_surjective :
    Function.Surjective
      (fun q : Polynomial (RatFunc k) => Polynomial.aeval η q) := by
  let pb := Field.powerBasisOfFiniteOfSeparable (RatFunc k) F
  have hgen : η = pb.gen := rfl
  intro x
  obtain ⟨q, hq⟩ := pb.exists_eq_aeval' x
  exact ⟨q, by rw [hgen]; exact hq.symm⟩
theorem separableGenerator_derivative_ne_zero :
    Polynomial.aeval η (μ).derivative ≠ 0 := by
  simpa only [separableGeneratorMinpoly] using
    Polynomial.Separable.aeval_derivative_ne_zero
      (Algebra.IsSeparable.isSeparable' η)
      (minpoly.aeval (RatFunc k) η)
noncomputable def separableGeneratorValue (D : Derivation k (RatFunc k) M) : M :=
  - ((Polynomial.aeval η (μ).derivative)⁻¹ •
    (μ).sum (fun n a => η ^ n • D a))
local notation3 "ν" => separableGeneratorValue (k := k) (F := F)
theorem polynomialExtensionValue_separableGeneratorMinpoly (D : Derivation k (RatFunc k) M) :
    polynomialExtensionValue D η (ν D) μ = 0 := by
  change (μ).sum (fun n a => η ^ n • D a)
    + Polynomial.aeval η (μ).derivative • ν D = 0
  rw [separableGeneratorValue, smul_neg, smul_smul,
    mul_inv_cancel₀ separableGenerator_derivative_ne_zero, one_smul, add_neg_cancel]
theorem polynomialExtensionDerivation_separableGenerator_kernel
    (D : Derivation k (RatFunc k) M) (q : Polynomial (RatFunc k))
    (hq : Polynomial.aeval η q = 0) :
    polynomialExtensionDerivation D η (ν D) q = 0 := by
  have hdiv : μ ∣ q := by
    simpa only [separableGeneratorMinpoly] using
      (minpoly.dvd_iff.mpr hq : minpoly (RatFunc k) η ∣ q)
  rcases hdiv with ⟨r, hr⟩
  rw [hr]
  change Module.AEval.of (RatFunc k) M η
    (polynomialExtensionValue D η (ν D) (μ * r)) = 0
  rw [polynomialExtensionValue_leibniz,
    show Polynomial.aeval η μ = 0 by
      simpa only [separableGeneratorMinpoly] using minpoly.aeval (RatFunc k) η,
    zero_smul, polynomialExtensionValue_separableGeneratorMinpoly, smul_zero, add_zero]
  simp
noncomputable def separableDerivationExtension (D : Derivation k (RatFunc k) M) :
    Derivation k F M :=
  descendPolynomialDerivation η
    (polynomialExtensionDerivation D η (ν D))
    separableGenerator_aeval_surjective
    (fun q hq => polynomialExtensionDerivation_separableGenerator_kernel D q hq)
theorem separableDerivationExtension_apply_algebraMap (D : Derivation k (RatFunc k) M)
    (a : RatFunc k) :
    separableDerivationExtension D (algebraMap (RatFunc k) F a) = D a := by
  rw [← Polynomial.aeval_C]
  rw [separableDerivationExtension, descendPolynomialDerivation_apply_aeval]
  rw [polynomialExtensionDerivation_C]
  rfl
theorem separableDerivationExtension_restrict (D : Derivation k (RatFunc k) M) :
    (separableDerivationExtension (k := k) (F := F) D).compAlgebraMap (RatFunc k) = D := by
  ext a
  exact separableDerivationExtension_apply_algebraMap (k := k) (F := F) D a
noncomputable def separableDerivationRestrictionEquiv :
    Derivation k F M ≃ₗ[F] Derivation k (RatFunc k) M :=
  LinearEquiv.ofBijective (Derivation.compAlgebraMapL k (RatFunc k) F M) ⟨
    fun D₁ D₂ h => extension_unique h,
    fun D => ⟨separableDerivationExtension (k := k) (F := F) D,
      separableDerivationExtension_restrict (k := k) (F := F) D⟩⟩
noncomputable def separableDerivationValueEquiv :
    Derivation k F M ≃ₗ[RatFunc k] M :=
  ((separableDerivationRestrictionEquiv (k := k) (F := F) (M := M)).restrictScalars
    (RatFunc k)).trans (RatFuncDerivation.rationalDerivationEquiv (k := k) (M := M))
end SeparableDerivationExtension
end QEC.Coding.AlgebraicGeometry


