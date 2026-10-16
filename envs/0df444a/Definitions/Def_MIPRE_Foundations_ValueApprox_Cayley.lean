-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
-- name    : MIPRE_Foundations_ValueApprox_Cayley
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:06:41.98824+00:00
-- url     : https://prove2.me/theorems/f3eb4e59-efbc-4bd0-83d1-1669373d7a2f
-- title:
--   The Cayley transform between skew-Hermitian matrices and unitaries
-- statement:
--   Let $n$ be a finite index type with decidable equality and consider complex $n \times n$ matrices. `MIPRE.ValueApprox.IsSkewHermitian S` is the predicate $S^{\mathsf H} = -S$ (conjugate transpose), and `MIPRE.ValueApprox.cayley S` is the Cayley transform
--   $$\mathrm{cayley}(S) = (1 - S)\,(1 + S)^{-1},$$
--   with Mathlib's matrix inverse (which is $0$ on a singular matrix, so the definition is total). This is the parametrization of unitaries by which the enumeration of `lem:value-lower-approx` reaches exact unitaries with Gaussian-rational entries: the Cayley transform of a skew-Hermitian matrix with Gaussian-rational entries has Gaussian-rational entries and the transform is $2$-Lipschitz (bundles `MIPRE_Foundations_ValueApprox_Gaussian` and `MIPRE_Foundations_ValueApprox_Norms`), so rounding $S$ entrywise approximates the unitary (blueprint `lem:rational-pvm-dense`).
--
--   The embedded lemmas: `IsSkewHermitian.neg`; `IsSkewHermitian.re_dotProduct_mulVec`, the quadratic form $\langle v, Sv\rangle$ of a skew-Hermitian matrix has real part $0$; `IsSkewHermitian.mulVec_one_add_eq_zero`, $(1+S)v = 0$ forces $v = 0$, whence `isUnit_one_add` and `isUnit_one_sub`, $1 + S$ and $1 - S$ are units; `cayley_eq`, $\mathrm{cayley}(S) = 2(1+S)^{-1} - 1$ when $1 + S$ is a unit; `cayley_mem_unitaryGroup`, the Cayley transform of a skew-Hermitian matrix is unitary; `exists_isSkewHermitian_cayley_eq`, every unitary $U$ with $1 + U$ a unit is $\mathrm{cayley}(S)$ for some skew-Hermitian $S$; `smul_mem_unitaryGroup` and `smul_mul_mul_conjTranspose_smul`, for $\|z\| = 1$ the matrix $zU$ is unitary when $U$ is, and $(zU)\,P\,(zU)^{\mathsf H} = U P U^{\mathsf H}$; `infinite_setOf_norm_eq_one`, the unit circle $\{z : \|z\| = 1\}$ is infinite; and `exists_norm_eq_one_isUnit_one_add_smul`, for every matrix $U$ some unit scalar $z$ makes $1 + zU$ a unit. Together: up to a phase, every unitary is a Cayley transform.
--
--   **Formalization Note**. `IsSkewHermitian` is a plain `Prop`-valued definition and unitarity is membership in `Matrix.unitaryGroup n ℂ`; `cayley` is `noncomputable` because of the matrix inverse, and invertibility of $1 + S$ enters the statements only through `IsUnit` hypotheses or conclusions. `IsSkewHermitian.neg` needs no finiteness, `re_dotProduct_mulVec` needs `Fintype n`, and the remaining lemmas also `DecidableEq n`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/Cayley.lean; blueprint lem:rational-pvm-dense

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/Cayley.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Cayley transform

`cayley S = (1 - S) * (1 + S)⁻¹` maps skew-Hermitian matrices to unitaries, and every
unitary `U` for which `1 + U` is invertible is `cayley S` for the skew-Hermitian
`S = (1 - U) * (1 + U)⁻¹`; multiplying `U` by a suitable unit scalar `z` always makes
`1 + z • U` invertible, and `(z • U) P (z • U)ᴴ = U P Uᴴ`, so up to a phase every unitary is a
Cayley transform. This is the parametrization of unitaries by which the enumeration of
`lem:value-lower-approx` reaches exact unitaries with Gaussian-rational entries: the Cayley
transform of a skew-Hermitian matrix with Gaussian-rational entries has Gaussian-rational
entries, and the transform is `2`-Lipschitz (`MIPRE.Foundations.ValueApprox.Norms`), so
rounding `S` entrywise approximates `U`.

The one analytic input is `IsSkewHermitian.mulVec_one_add_eq_zero`: for skew-Hermitian
`S`, `⟨v, S v⟩` is purely imaginary, so `(1 + S) v = 0` forces `v = 0`.
-/

namespace MIPRE.ValueApprox

open Matrix Polynomial
open scoped ComplexOrder

variable {n : Type*}

/-- Skew-Hermitian matrices: `Sᴴ = -S`. -/
def IsSkewHermitian (S : Matrix n n ℂ) : Prop := Sᴴ = -S

namespace IsSkewHermitian

variable {S : Matrix n n ℂ}

theorem neg (hS : IsSkewHermitian S) : IsSkewHermitian (-S) := by
  unfold IsSkewHermitian at *
  rw [conjTranspose_neg, hS]

variable [Fintype n]

/-- The quadratic form of a skew-Hermitian matrix is purely imaginary. -/
theorem re_dotProduct_mulVec (hS : IsSkewHermitian S) (v : n → ℂ) :
    (star v ⬝ᵥ (S *ᵥ v)).re = 0 := by
  have h : star (star v ⬝ᵥ (S *ᵥ v)) = -(star v ⬝ᵥ (S *ᵥ v)) := by
    conv_lhs => rw [← star_star (S *ᵥ v)]
    rw [star_dotProduct_star, star_star, star_mulVec, hS, Matrix.vecMul_neg, neg_dotProduct,
      ← dotProduct_mulVec]
  have := congrArg Complex.re h
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
  linarith

variable [DecidableEq n]

/-- `(1 + S) v = 0` forces `v = 0`, since `‖(1 + S) v‖² = ‖v‖² + ‖S v‖²`. -/
theorem mulVec_one_add_eq_zero (hS : IsSkewHermitian S) {v : n → ℂ} (h : (1 + S) *ᵥ v = 0) :
    v = 0 := by
  have hSv : S *ᵥ v = -v := by
    rw [Matrix.add_mulVec, one_mulVec] at h
    exact eq_neg_of_add_eq_zero_right h
  have hre := hS.re_dotProduct_mulVec v
  rw [hSv, dotProduct_neg, Complex.neg_re, neg_eq_zero] at hre
  have hnn : 0 ≤ star v ⬝ᵥ v := dotProduct_star_self_nonneg v
  have him : (star v ⬝ᵥ v).im = 0 := (Complex.nonneg_iff.mp hnn).2.symm
  have hz : star v ⬝ᵥ v = 0 := Complex.ext hre him
  exact dotProduct_star_self_eq_zero.mp hz

theorem isUnit_one_add (hS : IsSkewHermitian S) : IsUnit (1 + S) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have : (1 + S) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hS.mulVec_one_add_eq_zero this)

theorem isUnit_one_sub (hS : IsSkewHermitian S) : IsUnit (1 - S) := by
  have := hS.neg.isUnit_one_add
  rwa [← sub_eq_add_neg] at this

end IsSkewHermitian

variable [Fintype n] [DecidableEq n]

/-- The Cayley transform `(1 - S) * (1 + S)⁻¹`. -/
noncomputable def cayley (S : Matrix n n ℂ) : Matrix n n ℂ := (1 - S) * (1 + S)⁻¹

/-- `cayley S = 2 (1 + S)⁻¹ - 1` whenever `1 + S` is invertible. -/
theorem cayley_eq {S : Matrix n n ℂ} (h : IsUnit (1 + S)) :
    cayley S = (2 : ℂ) • (1 + S)⁻¹ - 1 := by
  have hdet : IsUnit (1 + S).det := (Matrix.isUnit_iff_isUnit_det _).mp h
  have h2 : (1 - S) = (2 : ℂ) • (1 : Matrix n n ℂ) - (1 + S) := by
    rw [two_smul]; abel
  unfold cayley
  rw [h2, sub_mul, smul_mul_assoc, Matrix.one_mul, Matrix.mul_nonsing_inv _ hdet]

/-- The Cayley transform of a skew-Hermitian matrix is unitary. -/
theorem cayley_mem_unitaryGroup {S : Matrix n n ℂ} (hS : IsSkewHermitian S) :
    cayley S ∈ Matrix.unitaryGroup n ℂ := by
  have hdet : IsUnit (1 + S).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_one_add
  have hdet' : IsUnit (1 - S).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_one_sub
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar : star (cayley S) = (1 - S)⁻¹ * (1 + S) := by
    unfold cayley
    rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_add,
      conjTranspose_sub, conjTranspose_one, hS, sub_neg_eq_add, ← sub_eq_add_neg]
  have hcomm : (1 + S) * (1 - S) = (1 - S) * (1 + S) := by
    simp only [mul_sub, sub_mul, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hstar]
  unfold cayley
  calc (1 - S)⁻¹ * (1 + S) * ((1 - S) * (1 + S)⁻¹)
      = (1 - S)⁻¹ * ((1 + S) * (1 - S)) * (1 + S)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (1 - S)⁻¹ * (1 - S) * ((1 + S) * (1 + S)⁻¹) := by
        rw [hcomm]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hdet', Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

/-- Every unitary `U` with `1 + U` invertible is the Cayley transform of the skew-Hermitian
matrix `(1 - U) * (1 + U)⁻¹`. -/
theorem exists_isSkewHermitian_cayley_eq {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (h1 : IsUnit (1 + U)) : ∃ S, IsSkewHermitian S ∧ cayley S = U := by
  have hdet : IsUnit (1 + U).det := (Matrix.isUnit_iff_isUnit_det _).mp h1
  have hUU : star U * U = 1 := (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hUU' : U * star U = 1 := (Matrix.mem_unitaryGroup_iff.mp hU)
  refine ⟨(2 : ℂ) • (1 + U)⁻¹ - 1, ?_, ?_⟩
  · -- skew-Hermitian: `(1 + U)⁻¹ᴴ = (1 + Uᴴ)⁻¹ = (1 + U)⁻¹ * U`, so
    -- `Sᴴ = 2 (1 + U)⁻¹ U - 1 = -(2 (1 + U)⁻¹ - 1)` because `2 (1+U)⁻¹ (1 + U) = 2`.
    unfold IsSkewHermitian
    have hinv : (1 + U)⁻¹ᴴ = (1 + U)⁻¹ * U := by
      rw [conjTranspose_nonsing_inv]
      apply Matrix.inv_eq_left_inv
      rw [conjTranspose_add, conjTranspose_one, Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_one,
        ← star_eq_conjTranspose, hUU', add_comm U 1, Matrix.nonsing_inv_mul _ hdet]
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hinv, Complex.star_def,
      map_ofNat]
    have h2 : (2 : ℂ) • ((1 + U)⁻¹ * U) = (2 : ℂ) • 1 - (2 : ℂ) • (1 + U)⁻¹ := by
      have : (1 + U)⁻¹ * U = 1 - (1 + U)⁻¹ := by
        have h3 : (1 + U)⁻¹ * (1 + U) = 1 := Matrix.nonsing_inv_mul _ hdet
        rw [Matrix.mul_add, Matrix.mul_one] at h3
        exact eq_sub_of_add_eq' h3
      rw [this, smul_sub]
    rw [h2, two_smul ℂ (1 : Matrix n n ℂ)]
    abel
  · -- `1 + S = 2 (1 + U)⁻¹` and `1 - S = 2 (1 + U)⁻¹ U`, so `cayley S = (1 + U)⁻¹ U (1 + U) = U`.
    have hmulU : (1 + U)⁻¹ * U = 1 - (1 + U)⁻¹ := by
      have h3 : (1 + U)⁻¹ * (1 + U) = 1 := Matrix.nonsing_inv_mul _ hdet
      rw [Matrix.mul_add, Matrix.mul_one] at h3
      exact eq_sub_of_add_eq' h3
    have h1S : (1 : Matrix n n ℂ) + ((2 : ℂ) • (1 + U)⁻¹ - 1) = (2 : ℂ) • (1 + U)⁻¹ := by abel
    have h2S : (1 : Matrix n n ℂ) - ((2 : ℂ) • (1 + U)⁻¹ - 1) = (2 : ℂ) • ((1 + U)⁻¹ * U) := by
      rw [hmulU, smul_sub, two_smul, two_smul]
      abel
    have hinv2 : ((2 : ℂ) • (1 + U)⁻¹)⁻¹ = (2⁻¹ : ℂ) • (1 + U) := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hdet]
      simp
    have hcomm : U * (1 + U) = (1 + U) * U := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    unfold cayley
    rw [h1S, h2S, hinv2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hcomm,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    simp

/-! ## Phases

`cayley` reaches only the unitaries `U` with `1 + U` invertible. Multiplying `U` by a unit
scalar `z` does not change the conjugation `P ↦ U P Uᴴ`, and some unit `z` always makes
`1 + z • U` invertible: `z ↦ det (1 + z • U)` is a polynomial with constant term `1`. -/

/-- `z • U` is unitary when `U` is and `‖z‖ = 1`. -/
theorem smul_mem_unitaryGroup {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) {z : ℂ}
    (hz : ‖z‖ = 1) : z • U ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  simp

omit [DecidableEq n] in
/-- Conjugating by `z • U` for a unit scalar `z` is conjugating by `U`. -/
theorem smul_mul_mul_conjTranspose_smul (U P : Matrix n n ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    (z • U) * P * (z • U)ᴴ = U * P * Uᴴ := by
  rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  simp

/-- The unit circle is infinite: `m ↦ (1 + m i) / (1 - m i)` is injective on `ℕ`. -/
theorem infinite_setOf_norm_eq_one : {z : ℂ | ‖z‖ = 1}.Infinite := by
  have hden : ∀ m : ℕ, (1 : ℂ) - (m : ℂ) * Complex.I ≠ 0 := fun m h => by
    have := congrArg Complex.re h
    simp at this
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => (1 + (m : ℂ) * Complex.I) / (1 - (m : ℂ) * Complex.I)) ?_ ?_
  · intro m m' h
    simp only at h
    rw [div_eq_div_iff (hden m) (hden m')] at h
    have him := congrArg Complex.im h
    simp at him
    have : (m : ℝ) = m' := by linarith
    exact_mod_cast this
  · intro m
    simp only [Set.mem_ofPred_eq, norm_div]
    have h1 : ‖(1 : ℂ) - (m : ℂ) * Complex.I‖ = ‖(1 : ℂ) + (m : ℂ) * Complex.I‖ := by
      rw [← Complex.norm_conj (1 + (m : ℂ) * Complex.I)]
      congr 1
      simp [Complex.conj_I, sub_eq_add_neg]
    rw [h1, div_self (norm_ne_zero_iff.mpr fun h => ?_)]
    have := congrArg Complex.re h
    simp at this

/-- Some unit scalar multiple `z • U` of any matrix has `1 + z • U` invertible:
`det (1 + z • U)` is a polynomial in `z` with constant term `1`, so it has finitely many roots,
while the unit circle is infinite. -/
theorem exists_norm_eq_one_isUnit_one_add_smul (U : Matrix n n ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ IsUnit (1 + z • U) := by
  set q : Polynomial ℂ := ((1 : Matrix n n (Polynomial ℂ)) + (X : Polynomial ℂ) • U.map C).det
    with hq
  have heval : ∀ z : ℂ, q.eval z = (1 + z • U).det := by
    intro z
    rw [hq, ← Polynomial.coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij] <;> ring
  have hq0 : q ≠ 0 := by
    intro h
    have h0 := heval 0
    rw [h, Polynomial.eval_zero, zero_smul, add_zero, Matrix.det_one] at h0
    exact zero_ne_one h0
  obtain ⟨z, hz, hroot⟩ :=
    infinite_setOf_norm_eq_one.exists_notMem_finite (Polynomial.finite_setOfPred_isRoot hq0)
  refine ⟨z, hz, ?_⟩
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← heval]
  exact hroot

end MIPRE.ValueApprox


