-- Prove2me | Definitions.Def_FltRegular_NumberTheory_KummersLemma_Field
-- name    : FltRegular_NumberTheory_KummersLemma_Field
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:32:19.967447+00:00
-- url     : https://prove2.me/theorems/77f70476-682e-460f-8264-549d31730f2f
-- title:
--   Field
-- statement:
--   Definitions and structural lemmas for Field, from leanprover-community/flt-regular contributors (see pinned LICENSE and source headers)'s pinned Fermat's Last Theorem for regular primes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/KummersLemma/Field.lean

module
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Unramified
set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped NumberField
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
variable (u : (𝓞 K)ˣ)
  (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ p ≠ u)
open Polynomial IsCyclotomicExtension.Rat
include hcong hp in
-- The cyclotomic-extension instance is retained for compatibility with existing callers.
@[nolint unusedArguments]
lemma zeta_sub_one_pow_dvd_poly [IsCyclotomicExtension {p} ℚ K] :
    C ((hζ.toInteger - 1 : 𝓞 K) ^ p) ∣
      (C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K) := by
  rw [← dvd_sub_left (_root_.map_dvd C hcong), add_sub_assoc, C.map_sub (u : 𝓞 K), ← sub_add,
    sub_self, map_one, zero_add]
  refine dvd_C_mul_X_sub_one_pow_add_one hpri.out hp _ _ dvd_rfl ?_
  have hassoc : Associated ((hζ.toInteger - 1 : 𝓞 K) ^ (p - 1)) p := by
    simpa only using associated_zeta_sub_one_pow_prime _ hζ
  convert mul_dvd_mul_right hassoc.dvd _
  rw [← pow_succ, tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]
namespace KummersLemma
omit [NumberField K] in
lemma natDegree_poly_aux :
    natDegree ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K)) = p := by
  rw [natDegree_add_C, natDegree_pow, ← C.map_one, natDegree_sub_C, natDegree_mul_X, natDegree_C,
    zero_add, mul_one]
  exact C_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)
omit [NumberField K] in
lemma monic_poly_aux :
    leadingCoeff ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K)) =
      (hζ.toInteger - 1 : 𝓞 K) ^ p := by
  trans leadingCoeff ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p)
  · rw [leadingCoeff, leadingCoeff, coeff_add]
    nth_rewrite 1 [natDegree_add_C]
    convert add_zero _ using 2
    rw [natDegree_poly_aux hζ, coeff_C, if_neg (NeZero.pos p).ne.symm]
  · rw [leadingCoeff_pow, ← C.map_one, leadingCoeff, natDegree_sub_C, natDegree_mul_X]
    · simp only [map_one, natDegree_C, zero_add, coeff_sub, coeff_mul_X, coeff_C,
        coeff_one, sub_zero, one_ne_zero, ↓reduceIte]
    · exact C_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)
variable [IsCyclotomicExtension {p} ℚ K]
noncomputable def poly : (𝓞 K)[X] := (zeta_sub_one_pow_dvd_poly hp hζ u hcong).choose
lemma poly_spec :
    C ((hζ.toInteger - 1 : 𝓞 K) ^ p) * poly hp hζ u hcong =
      (C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K) :=
  (zeta_sub_one_pow_dvd_poly hp hζ u hcong).choose_spec.symm
lemma monic_poly : Monic (poly hp hζ u hcong) := by
  have := congr_arg leadingCoeff (poly_spec hp hζ u hcong)
  simp only [map_pow, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_C,
    monic_poly_aux hζ] at this
  refine mul_right_injective₀ ?_ (this.trans (mul_one _).symm)
  exact pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)
theorem aeval_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (m : ℕ) :
    aeval (((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1))) (poly hp hζ u hcong) = 0 := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_sub, map_one]
  have := congr_arg (aeval ((1 - ζ ^ m • α) / (algebraMap K L (ζ - 1))))
    (poly_spec hp hζ u hcong)
  have hcoe : (algebraMap (𝓞 K) L) (↑hζ.toInteger) = algebraMap K L ζ := rfl
  have hcoe1 : (algebraMap (𝓞 K) L) ↑u = algebraMap K L ↑↑u := rfl
  simp only [map_sub, map_one, map_pow, map_mul, aeval_C, _root_.smul_pow, hcoe, e, hcoe1, map_add,
    aeval_X, ← mul_div_assoc, mul_div_cancel_left₀ _ hζ', sub_sub_cancel_left,
    (hpri.out.odd_of_ne_two hp).neg_pow] at this
  rw [← pow_mul, mul_comm m, pow_mul, hζ.pow_eq_one, one_pow, one_smul, neg_add_cancel,
    mul_eq_zero] at this
  exact this.resolve_left (pow_ne_zero _ hζ')
def polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (m : ℕ) : 𝓞 L :=
  ⟨((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1)), isIntegral_trans _
      ⟨poly hp hζ u hcong, monic_poly hp hζ u hcong, aeval_poly hp hζ u hcong α e m⟩⟩
end KummersLemma


