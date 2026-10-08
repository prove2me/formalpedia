-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFractionField_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianFractionField_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:47:03.169003+00:00
-- url     : https://prove2.me/theorems/fe4cf22d-55e6-4404-9edf-b4fc63b03dbd
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianFractionField source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianFractionField

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianFractionField
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalArithmetic_p0
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Discriminant

set_option autoImplicit false




/-!
# The Gaussian fraction field as a quadratic number field

The fraction field of `ℤ[i]` has the structural rational basis `(1,i)`.
The only localization point to check is that inverting nonzero ordinary
integers already inverts every nonzero Gaussian integer: `z` divides its
nonzero integer norm `z * star z`.

No embeddings or Gaussian elements are enumerated.
-/

open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix

namespace MazurProof.N13GaussianFractionField

noncomputable section

open N13GaussianGlobalArithmetic

/-- The Gaussian rational field. -/
abbrev K := FractionRing GI

@[simp] theorem i_mul_self :
    i * i = -1 := by
  simp [i, Zsqrtd.dmuld]

/-- The Gaussian generator is integral over the integers. -/
theorem i_integral : IsIntegral ℤ i := by
  refine ⟨X ^ 2 + C (1 : ℤ), ?_, ?_⟩
  · exact Polynomial.monic_X_pow_add_C (1 : ℤ)
      (by norm_num)
  · simp [i, pow_two, Zsqrtd.dmuld]

/-- Every Gaussian integer is integral over `ℤ`, structurally from its
decomposition `a + i b`. -/
instance gaussianIntIntegral :
    Algebra.IsIntegral ℤ GI where
  isIntegral := by
    rintro ⟨a, b⟩
    rw [Zsqrtd.decompose]
    exact
      (isIntegral_intCast a).add
        (i_integral.mul (isIntegral_intCast b))

/-! ## The integral basis `(1,i)` -/

/-- Gaussian real and imaginary coordinates as an additive equivalence. -/
def gaussianIntAddEquiv : GI ≃+ (Fin 2 → ℤ) where
  toFun := fun z j => Fin.cases z.re (fun _ => z.im) j
  invFun := fun v => ⟨v 0, v 1⟩
  left_inv := by
    intro z
    ext <;> rfl
  right_inv := by
    intro v
    funext j
    fin_cases j <;> rfl
  map_add' := by
    intro x y
    funext j
    fin_cases j <;> rfl

/-- The coordinate equivalence as an integer-linear equivalence. -/
def gaussianIntLinearEquiv : GI ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  gaussianIntAddEquiv.toIntLinearEquiv

/-- The structural integral basis `(1,i)` of the Gaussian integers. -/
def gaussianIntBasis : Basis (Fin 2) ℤ GI :=
  Basis.ofEquivFun gaussianIntLinearEquiv

instance gaussianIntFree : Module.Free ℤ GI :=
  Module.Free.of_basis gaussianIntBasis

instance gaussianIntFinite : Module.Finite ℤ GI :=
  Module.Finite.of_basis gaussianIntBasis

@[simp] theorem gaussianIntBasis_repr_apply
    (z : GI) (j : Fin 2) :
    gaussianIntBasis.repr z j =
      Fin.cases z.re (fun _ => z.im) j := by
  rfl

@[simp] theorem gaussianIntBasis_zero :
    gaussianIntBasis (0 : Fin 2) = 1 := by
  apply gaussianIntBasis.ext_elem
  intro j
  rw [gaussianIntBasis.repr_self_apply]
  fin_cases j <;> rfl

@[simp] theorem gaussianIntBasis_one :
    gaussianIntBasis (1 : Fin 2) = i := by
  apply gaussianIntBasis.ext_elem
  intro j
  rw [gaussianIntBasis.repr_self_apply]
  fin_cases j <;> rfl

/-! ## Cofinality of ordinary integer denominators -/

/-- Images of nonzero ordinary integers in `ℤ[i]`. -/
abbrev intDenoms : Submonoid GI :=
  Algebra.algebraMapSubmonoid GI (nonZeroDivisors ℤ)

theorem intDenoms_le_nonZeroDivisors :
    intDenoms ≤ nonZeroDivisors GI := by
  rintro _ ⟨n, hn, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact
    (RingHom.injective_int (algebraMap ℤ GI)).ne
      (nonZeroDivisors.ne_zero hn)

/-- Every nonzero Gaussian denominator divides a nonzero ordinary integer:
choose its norm. -/
theorem nonZeroGaussian_dvd_intDenom
    (z : GI) (hz : z ∈ nonZeroDivisors GI) :
    ∃ m ∈ intDenoms, z ∣ m := by
  have hz0 : z ≠ 0 :=
    nonZeroDivisors.ne_zero hz
  have hnorm0 : Zsqrtd.norm z ≠ 0 := by
    simpa using hz0
  refine ⟨(Zsqrtd.norm z : GI), ?_, ?_⟩
  · have hm : Zsqrtd.norm z ∈ nonZeroDivisors ℤ :=
      mem_nonZeroDivisors_iff_ne_zero.mpr hnorm0
    simpa [intDenoms] using
      (Algebra.mem_algebraMapSubmonoid_of_mem
        (S := GI)
        (⟨Zsqrtd.norm z, hm⟩ : nonZeroDivisors ℤ))
  · exact ⟨star z, Zsqrtd.norm_eq_mul_conj z⟩

/-- The Gaussian fraction field is also the localization obtained by
inverting only the nonzero ordinary integers. -/
instance intDenomLocalization :
    IsLocalization intDenoms K := by
  refine
    (IsLocalization.iff_of_le_of_exists_dvd
      (S := K)
      (M := intDenoms)
      (nonZeroDivisors GI)
      intDenoms_le_nonZeroDivisors
      ?_).2 inferInstance
  intro z hz
  exact nonZeroGaussian_dvd_intDenom z hz

/-! ## The localized rational basis -/

instance intRatAlgebraScalarTower :
    @IsScalarTower ℤ ℚ K
      (@Algebra.toSMul ℤ ℚ _ _ inferInstance)
      (@Algebra.toSMul ℚ K _ _ inferInstance)
      (@Algebra.toSMul ℤ K _ _ inferInstance) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    have hmaps :
        algebraMap ℤ K =
          (algebraMap ℚ K).comp (algebraMap ℤ ℚ) :=
      RingHom.ext_int _ _
    exact DFunLike.congr_fun hmaps z

/-- The rational basis `(1,i)` of `Frac(ℤ[i])`. -/
def gaussianBasis : Basis (Fin 2) ℚ K :=
  Basis.localizationLocalization
    ℚ (nonZeroDivisors ℤ) K gaussianIntBasis

@[simp] theorem gaussianBasis_apply (j : Fin 2) :
    gaussianBasis j =
      algebraMap GI K (gaussianIntBasis j) :=
  Basis.localizationLocalization_apply
    ℚ (nonZeroDivisors ℤ) K gaussianIntBasis j

/-- The Gaussian generator in its fraction field. -/
def iK : K :=
  algebraMap GI K i

@[simp] theorem gaussianBasis_zero :
    gaussianBasis (0 : Fin 2) = 1 := by
  simp [gaussianBasis]

@[simp] theorem gaussianBasis_one :
    gaussianBasis (1 : Fin 2) = iK := by
  simp [gaussianBasis, iK]

@[simp] theorem iK_mul_self :
    iK * iK = -1 := by
  change algebraMap GI K i * algebraMap GI K i = -1
  rw [← map_mul, i_mul_self, map_neg, map_one]

@[simp] theorem gaussianBasis_repr_algebraMap
    (z : GI) (j : Fin 2) :
    gaussianBasis.repr (algebraMap GI K z) j =
      algebraMap ℤ ℚ (gaussianIntBasis.repr z j) :=
  Basis.localizationLocalization_repr_algebraMap
    ℚ (nonZeroDivisors ℤ) K gaussianIntBasis z j

instance gaussianFiniteDimensional :
    FiniteDimensional ℚ K :=
  Module.Finite.of_basis gaussianBasis

theorem finrank_K :
    Module.finrank ℚ K = 2 := by
  rw [Module.finrank_eq_card_basis gaussianBasis]
  simp

instance gaussianNumberField : NumberField K where
  to_charZero := inferInstance
  to_finiteDimensional := gaussianFiniteDimensional

/-! ## Power basis, minimal polynomial, and discriminant -/

/-- The quadratic polynomial of the Gaussian generator. -/
def gaussianMinpoly : ℚ[X] :=
  X ^ 2 + 1

/-- The rational basis `(1,i)` is the power basis generated by `i`. -/
def gaussianPowerBasis : PowerBasis ℚ K where
  gen := iK
  dim := 2
  basis := gaussianBasis
  basis_eq_pow := by
    intro j
    fin_cases j
    · simp
    · simpa using gaussianBasis_one

@[simp] theorem gaussianPowerBasis_gen :
    gaussianPowerBasis.gen = iK := rfl

@[simp] theorem gaussianPowerBasis_dim :
    gaussianPowerBasis.dim = 2 := rfl

@[simp] theorem gaussianPowerBasis_basis :
    gaussianPowerBasis.basis = gaussianBasis := rfl

theorem gaussianMinpoly_monic :
    gaussianMinpoly.Monic := by
  simpa [gaussianMinpoly] using
    (Polynomial.monic_X_pow_add_C (1 : ℚ)
      (show (2 : ℕ) ≠ 0 by decide))

@[simp] theorem aeval_gaussianMinpoly :
    Polynomial.aeval iK gaussianMinpoly = 0 := by
  simp [gaussianMinpoly, pow_two, iK_mul_self]

theorem gaussianMinpoly_degree :
    gaussianMinpoly.degree = ((2 : ℕ) : WithBot ℕ) := by
  change Polynomial.degree ((X : ℚ[X]) ^ 2 + C 1) =
    ((2 : ℕ) : WithBot ℕ)
  rw [Polynomial.degree_add_C (by simp)]
  simp

theorem minpoly_iK :
    minpoly ℚ iK = gaussianMinpoly := by
  symm
  apply minpoly.unique_of_degree_le_degree_minpoly ℚ iK
  · exact gaussianMinpoly_monic
  · exact aeval_gaussianMinpoly
  · have hdeg :
        (minpoly ℚ iK).degree =
          ((2 : ℕ) : WithBot ℕ) := by
      simpa only [gaussianPowerBasis_gen,
        gaussianPowerBasis_dim] using
        (PowerBasis.degree_minpoly gaussianPowerBasis)
    rw [gaussianMinpoly_degree, hdeg]

@[simp] theorem gaussianMinpoly_nextCoeff :
    gaussianMinpoly.nextCoeff = 0 := by
  have hnat : gaussianMinpoly.natDegree = 2 := by
    unfold gaussianMinpoly
    compute_degree!
  rw [Polynomial.nextCoeff_of_natDegree_pos (by omega), hnat]
  simp [gaussianMinpoly, Polynomial.coeff_one]

@[simp] theorem trace_iK :
    Algebra.trace ℚ K iK = 0 := by
  have h :=
    PowerBasis.trace_gen_eq_nextCoeff_minpoly gaussianPowerBasis
  simpa only [gaussianPowerBasis_gen, minpoly_iK,
    gaussianMinpoly_nextCoeff, neg_zero] using h

@[simp] theorem trace_one_gaussian :
    Algebra.trace ℚ K (1 : K) = 2 := by
  simpa using
    (Algebra.trace_algebraMap_of_basis gaussianBasis (1 : ℚ))

@[simp] theorem trace_neg_one_gaussian :
    Algebra.trace ℚ K (-1 : K) = -2 := by
  simp

/-- The discriminant of the structural Gaussian basis `(1,i)`. -/
theorem discr_gaussianBasis :
    Algebra.discr ℚ gaussianBasis = -4 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, gaussianBasis_zero,
    gaussianBasis_one, one_mul, mul_one, iK_mul_self,
    trace_one_gaussian, trace_iK, trace_neg_one_gaussian]
  norm_num

/-- The integral Gaussian basis has the same discriminant `-4`.
This follows by localizing the basis, not by recomputing its trace matrix. -/
theorem discr_gaussianIntBasis :
    Algebra.discr ℤ gaussianIntBasis = -4 := by
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.discr_localizationLocalization
    ℤ (nonZeroDivisors ℤ) K gaussianIntBasis]
  exact discr_gaussianBasis

/-- The algebra norm in the integral basis `(1,i)` is the usual Gaussian
norm.  The proof is the symbolic determinant of multiplication by
`a + bi`, not a computation on Gaussian elements. -/
theorem algebraNorm_eq_gaussianNorm (z : GI) :
    Algebra.norm ℤ z = Zsqrtd.norm z := by
  rw [Algebra.norm_eq_matrix_det gaussianIntBasis,
    Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    gaussianIntBasis_zero, gaussianIntBasis_one,
    gaussianIntBasis_repr_apply, i]
  change z.re * z.re + z.im * z.im = Zsqrtd.norm z
  simp [Zsqrtd.norm]

@[simp] theorem algebraNorm_pi :
    Algebra.norm ℤ pi = 13 := by
  rw [algebraNorm_eq_gaussianNorm, pi_norm]

@[simp] theorem algebraNorm_pi_sq :
    Algebra.norm ℤ (pi ^ 2) = 13 ^ 2 := by
  rw [map_pow, algebraNorm_pi]

/-- Localization identifies the field norm on `K/ℚ` with the same Gaussian
norm. -/
theorem fieldNorm_algebraMap (z : GI) :
    Algebra.norm ℚ (algebraMap GI K z) =
      algebraMap ℤ ℚ (Zsqrtd.norm z) := by
  rw [Algebra.norm_localization
    ℤ (nonZeroDivisors ℤ) z,
    algebraNorm_eq_gaussianNorm]

@[simp] theorem fieldNorm_pi :
    Algebra.norm ℚ (algebraMap GI K pi) = 13 := by
  rw [fieldNorm_algebraMap, pi_norm]
  norm_num

@[simp] theorem fieldNorm_pi_sq :
    Algebra.norm ℚ (algebraMap GI K (pi ^ 2)) =
      13 ^ 2 := by
  rw [map_pow (algebraMap GI K),
    map_pow (Algebra.norm ℚ), fieldNorm_pi]

end

end MazurProof.N13GaussianFractionField


