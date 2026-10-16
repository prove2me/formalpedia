-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
-- name    : MIPRE_Foundations_ValueApprox_Norms
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:08:28.998318+00:00
-- url     : https://prove2.me/theorems/dbb073f0-486c-4e04-9d75-d5f6996079f4
-- title:
--   Operator-norm estimates for the enumeration of strategies
-- statement:
--   This bundle contributes no definitions; it is the analytic input of `lem:value-lower-approx`, 24 lemmas in the $L^{2}$ operator norm on complex $n \times n$ matrices (Mathlib's scoped `Matrix.Norms.L2Operator`), vectors $x : n \to \mathbb{C}$ being measured as `toLp 2 x` in Euclidean space, written $\|x\|$; $n$, $m$ are finite types with decidable equality (blueprint `lem:rational-pvm-dense`).
--
--   **Vectors.** `inner_toLp_toLp` ($\langle x, y\rangle = x^{*}\cdot y$), `norm_sq_toLp`, `dotProduct_star_self_eq_ofReal`, `norm_toLp_eq_one_of_dotProduct`, `norm_toLp_mulVec_le`, `norm_dotProduct_mulVec_le` ($|x^{*}\cdot(Ty)| \le \|T\|\,\|x\|\,\|y\|$), `l2_opNorm_le_of_forall` ($\|Ax\| \le c\,\|x\|$ for all $x$, $c \ge 0$, gives $\|A\| \le c$), `norm_toLp_le_card_mul_of_forall_norm_le` (entries bounded by $\delta \ge 0$ give $\|v\| \le |n|\,\delta$) and `norm_toLp_normalize_sub_le` ($\|u/\|u\| - \psi\| \le 2\,\|u - \psi\|$ for $\|\psi\| = 1$, $u \ne 0$).
--
--   **The Cayley transform.** `IsSkewHermitian.norm_toLp_le_norm_toLp_one_add_mulVec` ($\|x\| \le \|(1+S)x\|$), `IsSkewHermitian.norm_inv_one_add_le` ($\|(1+S)^{-1}\| \le 1$), the resolvent identity `cayley_sub_cayley`, $\mathrm{cayley}(S) - \mathrm{cayley}(T) = 2\,(1+S)^{-1}(T - S)(1+T)^{-1}$, and `norm_cayley_sub_cayley_le`,
--   $$\|\mathrm{cayley}(S) - \mathrm{cayley}(T)\| \le 2\,\|S - T\| \quad\text{for skew-Hermitian } S, T.$$
--
--   **Entrywise bounds, Kronecker products, unitaries, projections.** `l2_opNorm_le_card_mul_of_entry_le` ($|E_{ij}| \le \delta$ for all $i, j$ gives $\|E\| \le |n|\,\delta$); `kronecker_one_mulVec`, `one_kronecker_mulVec`, `norm_kronecker_one_le`, `norm_one_kronecker_le`, `norm_kronecker_le` ($\|X \otimes Y\| \le \|X\|\,\|Y\|$); `norm_mul_mul_conjTranspose_sub_le` ($\|VPV^{\mathsf H} - WPW^{\mathsf H}\| \le 2\,\|V - W\|$ when $\|V\|, \|W\|, \|P\| \le 1$); `norm_toLp_mulVec_eq_of_mem_unitaryGroup`, `norm_le_one_of_mem_unitaryGroup` (a unitary preserves vector norms and has norm at most $1$); `norm_le_one_of_isProj` (a self-adjoint idempotent has norm at most $1$) and `IsPVM.norm_le_one`.
--
--   **Formalization Note**. The matrix norm is the $L^{2}$ operator norm, enabled by `open scoped Matrix.Norms.L2Operator`, and every vector norm goes through `toLp 2` into `EuclideanSpace ℂ n`. All inequalities are non-strict, with the constants $2$ and $|n| = $ `Fintype.card n` as stated; `IsPVM.norm_sum_le_one`, named in the module docstring, is not among the declarations of this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/Norms.lean; blueprint lem:rational-pvm-dense

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/Norms.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective

/-!
# Operator-norm estimates for the enumeration of strategies

The analytic input of `lem:value-lower-approx`, in the L2 operator norm on matrices
(`Matrix.Norms.L2Operator`), with vectors `x : n → ℂ` measured in `ℂ^n` as `toLp 2 x`:

* `IsSkewHermitian.norm_inv_one_add_le`: `‖(1 + S)⁻¹‖ ≤ 1` for skew-Hermitian `S`;
* `norm_cayley_sub_cayley_le`: the Cayley transform is `2`-Lipschitz on skew-Hermitian
  matrices;
* `l2_opNorm_le_card_mul_of_entry_le`: an entrywise bound `δ` gives `‖E‖ ≤ n δ`, which is what
  rounding a matrix entrywise costs;
* unitaries and projections have norm at most `1` (`norm_le_one_of_mem_unitaryGroup`,
  `norm_le_one_of_isProj`), and so do the subset sums of a projective measurement
  (`IsPVM.norm_sum_le_one`).
-/

namespace MIPRE.ValueApprox

open Matrix WithLp
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Vectors of `ℂ^n` -/

omit [DecidableEq n] in
theorem inner_toLp_toLp (x y : n → ℂ) :
    ⟪(toLp 2 x : EuclideanSpace ℂ n), (toLp 2 y : EuclideanSpace ℂ n)⟫_ℂ = star x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

omit [DecidableEq n] in
theorem norm_sq_toLp (x : n → ℂ) :
    ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 = (star x ⬝ᵥ x).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (toLp 2 x : EuclideanSpace ℂ n), inner_toLp_toLp]
  exact RCLike.re_to_complex

omit [DecidableEq n] in
/-- `⟨x, x⟩ = ‖x‖²`, as a complex number. -/
theorem dotProduct_star_self_eq_ofReal (x : n → ℂ) :
    star x ⬝ᵥ x = ((‖(toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re, norm_sq_toLp]
  · rw [Complex.ofReal_im]
    exact (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg x)).2.symm

omit [DecidableEq n] in
theorem norm_toLp_eq_one_of_dotProduct {x : n → ℂ} (h : star x ⬝ᵥ x = 1) :
    ‖(toLp 2 x : EuclideanSpace ℂ n)‖ = 1 := by
  have hsq := norm_sq_toLp x
  rw [h, Complex.one_re] at hsq
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq

theorem norm_toLp_mulVec_le (A : Matrix n n ℂ) (x : n → ℂ) :
    ‖(toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ≤ ‖A‖ * ‖(toLp 2 x : EuclideanSpace ℂ n)‖ := by
  have h := (toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (toLp 2 x)
  rwa [toEuclideanCLM_toLp, l2_opNorm_toEuclideanCLM] at h

/-- `|⟨x, T y⟩| ≤ ‖T‖ ‖x‖ ‖y‖`. -/
theorem norm_dotProduct_mulVec_le (T : Matrix n n ℂ) (x y : n → ℂ) :
    ‖star x ⬝ᵥ (T *ᵥ y)‖ ≤
      ‖T‖ * ‖(toLp 2 x : EuclideanSpace ℂ n)‖ * ‖(toLp 2 y : EuclideanSpace ℂ n)‖ := by
  rw [← inner_toLp_toLp]
  calc ‖⟪(toLp 2 x : EuclideanSpace ℂ n), (toLp 2 (T *ᵥ y) : EuclideanSpace ℂ n)⟫_ℂ‖
      ≤ ‖(toLp 2 x : EuclideanSpace ℂ n)‖ * ‖(toLp 2 (T *ᵥ y) : EuclideanSpace ℂ n)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖(toLp 2 x : EuclideanSpace ℂ n)‖ * (‖T‖ * ‖(toLp 2 y : EuclideanSpace ℂ n)‖) := by
        gcongr
        exact norm_toLp_mulVec_le T y
    _ = _ := by ring

/-- The operator norm is bounded by any uniform bound on vectors. -/
theorem l2_opNorm_le_of_forall {A : Matrix n n ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : n → ℂ, ‖(toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)‖ ≤
      c * ‖(toLp 2 x : EuclideanSpace ℂ n)‖) : ‖A‖ ≤ c := by
  rw [← l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have e : toEuclideanCLM (n := n) (𝕜 := ℂ) A x = toLp 2 (A *ᵥ ofLp x) := by
    rw [← toEuclideanCLM_toLp, toLp_ofLp]
  rw [e]
  simpa using h (ofLp x)

/-! ## Skew-Hermitian matrices and the Cayley transform -/

namespace IsSkewHermitian

variable {S T : Matrix n n ℂ}

/-- `‖(1 + S) x‖ ≥ ‖x‖` for skew-Hermitian `S`: the cross term of `‖x + S x‖²` vanishes. -/
theorem norm_toLp_le_norm_toLp_one_add_mulVec (hS : IsSkewHermitian S) (x : n → ℂ) :
    ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ≤
      ‖(toLp 2 ((1 + S) *ᵥ x) : EuclideanSpace ℂ n)‖ := by
  have hsq : ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 ≤
      ‖(toLp 2 ((1 + S) *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 := by
    rw [Matrix.add_mulVec, one_mulVec, toLp_add, norm_add_sq (𝕜 := ℂ), inner_toLp_toLp,
      RCLike.re_to_complex, hS.re_dotProduct_mulVec, mul_zero, add_zero]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- `‖(1 + S)⁻¹‖ ≤ 1` for skew-Hermitian `S`. -/
theorem norm_inv_one_add_le (hS : IsSkewHermitian S) : ‖(1 + S)⁻¹‖ ≤ 1 := by
  refine l2_opNorm_le_of_forall zero_le_one fun x => ?_
  rw [one_mul]
  have hdet : IsUnit (1 + S).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_one_add
  have hx : (1 + S) *ᵥ ((1 + S)⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  calc ‖(toLp 2 ((1 + S)⁻¹ *ᵥ x) : EuclideanSpace ℂ n)‖
      ≤ ‖(toLp 2 ((1 + S) *ᵥ ((1 + S)⁻¹ *ᵥ x)) : EuclideanSpace ℂ n)‖ :=
        hS.norm_toLp_le_norm_toLp_one_add_mulVec _
    _ = ‖(toLp 2 x : EuclideanSpace ℂ n)‖ := by rw [hx]

end IsSkewHermitian

/-- The resolvent identity for the Cayley transform. -/
theorem cayley_sub_cayley {S T : Matrix n n ℂ} (hS : IsSkewHermitian S) (hT : IsSkewHermitian T) :
    cayley S - cayley T = (2 : ℂ) • ((1 + S)⁻¹ * (T - S) * (1 + T)⁻¹) := by
  rw [cayley_eq hS.isUnit_one_add, cayley_eq hT.isUnit_one_add, sub_sub_sub_cancel_right,
    ← smul_sub]
  congr 1
  have hdS := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit_one_add
  have hdT := (Matrix.isUnit_iff_isUnit_det _).mp hT.isUnit_one_add
  have h : T - S = (1 + T) - (1 + S) := by abel
  rw [h, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (1 + S)⁻¹ (1 + T) (1 + T)⁻¹,
    Matrix.mul_nonsing_inv _ hdT, Matrix.mul_one, Matrix.nonsing_inv_mul _ hdS, Matrix.one_mul]

/-- The Cayley transform is `2`-Lipschitz on skew-Hermitian matrices. -/
theorem norm_cayley_sub_cayley_le {S T : Matrix n n ℂ} (hS : IsSkewHermitian S)
    (hT : IsSkewHermitian T) : ‖cayley S - cayley T‖ ≤ 2 * ‖S - T‖ := by
  have h3 : ‖(1 + S)⁻¹ * (T - S) * (1 + T)⁻¹‖ ≤ ‖S - T‖ := by
    calc ‖(1 + S)⁻¹ * (T - S) * (1 + T)⁻¹‖ ≤ ‖(1 + S)⁻¹‖ * ‖T - S‖ * ‖(1 + T)⁻¹‖ :=
          norm_mul₃_le
      _ ≤ 1 * ‖T - S‖ * 1 := by
          gcongr
          · exact hS.norm_inv_one_add_le
          · exact hT.norm_inv_one_add_le
      _ = ‖S - T‖ := by rw [one_mul, mul_one, norm_sub_rev]
  rw [cayley_sub_cayley hS hT, norm_smul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith

/-! ## Entrywise bounds -/

/-- An entrywise bound gives an operator-norm bound with a factor of the dimension. -/
theorem l2_opNorm_le_card_mul_of_entry_le {E : Matrix n n ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i j, ‖E i j‖ ≤ δ) : ‖E‖ ≤ Fintype.card n * δ := by
  refine l2_opNorm_le_of_forall (by positivity) fun x => ?_
  have hrow : ∀ i, ‖(E *ᵥ x) i‖ ≤ δ * ∑ j, ‖x j‖ := fun i => by
    simp only [mulVec, dotProduct]
    calc ‖∑ j, E i j * x j‖ ≤ ∑ j, ‖E i j * x j‖ := norm_sum_le _ _
      _ = ∑ j, ‖E i j‖ * ‖x j‖ := by simp
      _ ≤ ∑ j, δ * ‖x j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
      _ = δ * ∑ j, ‖x j‖ := by rw [Finset.mul_sum]
  have hcs : (∑ j, ‖x j‖) ^ 2 ≤ Fintype.card n * ∑ j, ‖x j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖x j‖)
  have hsq : ‖(toLp 2 (E *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 ≤
      (Fintype.card n * δ * ‖(toLp 2 x : EuclideanSpace ℂ n)‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(E *ᵥ x) i‖ ^ 2 ≤ ∑ i, (δ * ∑ j, ‖x j‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
      _ = Fintype.card n * (δ ^ 2 * (∑ j, ‖x j‖) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow]
      _ ≤ Fintype.card n * (δ ^ 2 * (Fintype.card n * ∑ j, ‖x j‖ ^ 2)) := by gcongr
      _ = (Fintype.card n * δ) ^ 2 * ∑ j, ‖x j‖ ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-! ## Vectors with small entries -/

omit [DecidableEq n] in
/-- An entrywise bound on a vector gives a norm bound with a factor of the dimension. -/
theorem norm_toLp_le_card_mul_of_forall_norm_le {v : n → ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i, ‖v i‖ ≤ δ) : ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ≤ Fintype.card n * δ := by
  have hsq : ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 ≤ (Fintype.card n * δ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : n, δ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = Fintype.card n * δ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Fintype.card n : ℝ) ^ 2 * δ ^ 2 := by
          gcongr
          exact_mod_cast Nat.le_self_pow two_ne_zero _
      _ = (Fintype.card n * δ) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

omit [DecidableEq n] in
/-- Normalizing a vector `u` near a unit vector `ψ` keeps it near `ψ`:
`‖u / ‖u‖ - ψ‖ ≤ 2 ‖u - ψ‖`. -/
theorem norm_toLp_normalize_sub_le (u ψ : n → ℂ)
    (hψ : ‖(toLp 2 ψ : EuclideanSpace ℂ n)‖ = 1) (hu : u ≠ 0) :
    ‖(toLp 2 (((‖(toLp 2 u : EuclideanSpace ℂ n)‖ : ℂ)⁻¹) • u - ψ) : EuclideanSpace ℂ n)‖ ≤
      2 * ‖(toLp 2 (u - ψ) : EuclideanSpace ℂ n)‖ := by
  set r : ℝ := ‖(toLp 2 u : EuclideanSpace ℂ n)‖ with hr
  have hrpos : 0 < r := norm_pos_iff.mpr (by simpa using hu)
  have h1 : (toLp 2 ((r : ℂ)⁻¹ • u - ψ) : EuclideanSpace ℂ n) =
      ((r : ℂ)⁻¹ • toLp 2 u - toLp 2 u) + (toLp 2 u - toLp 2 ψ) := by
    rw [toLp_sub, toLp_smul]
    abel
  have h2 : ‖(r : ℂ)⁻¹ • (toLp 2 u : EuclideanSpace ℂ n) - toLp 2 u‖ ≤
      ‖(toLp 2 (u - ψ) : EuclideanSpace ℂ n)‖ := by
    have e : (r : ℂ)⁻¹ • (toLp 2 u : EuclideanSpace ℂ n) - toLp 2 u =
        (((r⁻¹ - 1 : ℝ)) : ℂ) • toLp 2 u := by
      push_cast
      rw [sub_smul, one_smul]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |r⁻¹ - 1| * r = |(r⁻¹ - 1) * r| := by rw [abs_mul, abs_of_pos hrpos]
      _ = |1 - r| := by rw [sub_mul, inv_mul_cancel₀ hrpos.ne', one_mul]
      _ = |‖(toLp 2 ψ : EuclideanSpace ℂ n)‖ - ‖(toLp 2 u : EuclideanSpace ℂ n)‖| := by
          rw [hψ]
      _ ≤ ‖(toLp 2 ψ : EuclideanSpace ℂ n) - toLp 2 u‖ := abs_norm_sub_norm_le _ _
      _ = ‖(toLp 2 (u - ψ) : EuclideanSpace ℂ n)‖ := by rw [norm_sub_rev, toLp_sub]
  have h3 : ‖(toLp 2 u : EuclideanSpace ℂ n) - toLp 2 ψ‖ =
      ‖(toLp 2 (u - ψ) : EuclideanSpace ℂ n)‖ := by rw [toLp_sub]
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  linarith

/-! ## Kronecker products -/

section Kronecker

open scoped Kronecker

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
theorem kronecker_one_mulVec (X : Matrix m m ℂ) (v : m × n → ℂ) (i : m) (j : n) :
    ((X ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v) (i, j) = (X *ᵥ fun k => v (k, j)) i := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [DecidableEq n] in
theorem one_kronecker_mulVec (Y : Matrix n n ℂ) (v : m × n → ℂ) (i : m) (j : n) :
    (((1 : Matrix m m ℂ) ⊗ₖ Y) *ᵥ v) (i, j) = (Y *ᵥ fun l => v (i, l)) j := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- `‖X ⊗ 1‖ ≤ ‖X‖`: `X ⊗ 1` acts as `X` on each column. -/
theorem norm_kronecker_one_le (X : Matrix m m ℂ) : ‖X ⊗ₖ (1 : Matrix n n ℂ)‖ ≤ ‖X‖ := by
  refine l2_opNorm_le_of_forall (norm_nonneg _) fun v => ?_
  have hsq : ‖(toLp 2 ((X ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v) : EuclideanSpace ℂ (m × n))‖ ^ 2 ≤
      (‖X‖ * ‖(toLp 2 v : EuclideanSpace ℂ (m × n))‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ j, ∑ i, ‖((X ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v) (i, j)‖ ^ 2
        = ∑ j, ‖(toLp 2 (X *ᵥ fun k => v (k, j)) : EuclideanSpace ℂ m)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [EuclideanSpace.norm_sq_eq]
          exact Finset.sum_congr rfl fun i _ => by rw [kronecker_one_mulVec]
      _ ≤ ∑ j, (‖X‖ * ‖(toLp 2 fun k => v (k, j) : EuclideanSpace ℂ m)‖) ^ 2 :=
          Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_mulVec_le X _) 2
      _ = ‖X‖ ^ 2 * ∑ i, ∑ j, ‖v (i, j)‖ ^ 2 := by
          simp only [mul_pow, EuclideanSpace.norm_sq_eq]
          rw [← Finset.mul_sum, Finset.sum_comm]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- `‖1 ⊗ Y‖ ≤ ‖Y‖`: `1 ⊗ Y` acts as `Y` on each row. -/
theorem norm_one_kronecker_le (Y : Matrix n n ℂ) : ‖(1 : Matrix m m ℂ) ⊗ₖ Y‖ ≤ ‖Y‖ := by
  refine l2_opNorm_le_of_forall (norm_nonneg _) fun v => ?_
  have hsq : ‖(toLp 2 (((1 : Matrix m m ℂ) ⊗ₖ Y) *ᵥ v) : EuclideanSpace ℂ (m × n))‖ ^ 2 ≤
      (‖Y‖ * ‖(toLp 2 v : EuclideanSpace ℂ (m × n))‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    calc ∑ i, ∑ j, ‖(((1 : Matrix m m ℂ) ⊗ₖ Y) *ᵥ v) (i, j)‖ ^ 2
        = ∑ i, ‖(toLp 2 (Y *ᵥ fun l => v (i, l)) : EuclideanSpace ℂ n)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [EuclideanSpace.norm_sq_eq]
          exact Finset.sum_congr rfl fun j _ => by rw [one_kronecker_mulVec]
      _ ≤ ∑ i, (‖Y‖ * ‖(toLp 2 fun l => v (i, l) : EuclideanSpace ℂ n)‖) ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_mulVec_le Y _) 2
      _ = ‖Y‖ ^ 2 * ∑ i, ∑ j, ‖v (i, j)‖ ^ 2 := by
          simp only [mul_pow, EuclideanSpace.norm_sq_eq]
          rw [← Finset.mul_sum]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The L2 operator norm is submultiplicative for Kronecker products. -/
theorem norm_kronecker_le (X : Matrix m m ℂ) (Y : Matrix n n ℂ) : ‖X ⊗ₖ Y‖ ≤ ‖X‖ * ‖Y‖ := by
  have h : X ⊗ₖ Y = (X ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ Y) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [h]
  calc ‖(X ⊗ₖ (1 : Matrix n n ℂ)) * ((1 : Matrix m m ℂ) ⊗ₖ Y)‖
      ≤ ‖X ⊗ₖ (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix m m ℂ) ⊗ₖ Y‖ := norm_mul_le _ _
    _ ≤ ‖X‖ * ‖Y‖ :=
        mul_le_mul (norm_kronecker_one_le X) (norm_one_kronecker_le Y) (norm_nonneg _)
          (norm_nonneg _)

end Kronecker

/-! ## Conjugation -/

/-- `V P Vᴴ` is `2`-Lipschitz in `V` when all matrices have norm at most `1`. -/
theorem norm_mul_mul_conjTranspose_sub_le {V W P : Matrix n n ℂ} (hV : ‖V‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    (hP : ‖P‖ ≤ 1) : ‖V * P * Vᴴ - W * P * Wᴴ‖ ≤ 2 * ‖V - W‖ := by
  have h : V * P * Vᴴ - W * P * Wᴴ = (V - W) * P * Vᴴ + W * P * (V - W)ᴴ := by
    rw [conjTranspose_sub]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [h]
  calc ‖(V - W) * P * Vᴴ + W * P * (V - W)ᴴ‖
      ≤ ‖(V - W) * P * Vᴴ‖ + ‖W * P * (V - W)ᴴ‖ := norm_add_le _ _
    _ ≤ ‖V - W‖ * ‖P‖ * ‖Vᴴ‖ + ‖W‖ * ‖P‖ * ‖(V - W)ᴴ‖ := add_le_add norm_mul₃_le norm_mul₃_le
    _ ≤ ‖V - W‖ * 1 * 1 + 1 * 1 * ‖V - W‖ := by
        rw [l2_opNorm_conjTranspose, l2_opNorm_conjTranspose]
        gcongr
    _ = 2 * ‖V - W‖ := by ring

/-! ## Unitaries and projections -/

theorem norm_toLp_mulVec_eq_of_mem_unitaryGroup {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (x : n → ℂ) :
    ‖(toLp 2 (U *ᵥ x) : EuclideanSpace ℂ n)‖ = ‖(toLp 2 x : EuclideanSpace ℂ n)‖ := by
  have h : ‖(toLp 2 (U *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 =
      ‖(toLp 2 x : EuclideanSpace ℂ n)‖ ^ 2 := by
    rw [norm_sq_toLp, norm_sq_toLp, ← dotProduct_conjTranspose_mul_self,
      ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU, one_mulVec]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem norm_le_one_of_mem_unitaryGroup {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    ‖U‖ ≤ 1 :=
  l2_opNorm_le_of_forall zero_le_one fun x => by
    rw [norm_toLp_mulVec_eq_of_mem_unitaryGroup hU, one_mul]

/-- A self-adjoint idempotent has norm at most `1`. -/
theorem norm_le_one_of_isProj {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) : ‖P‖ ≤ 1 := by
  refine l2_opNorm_le_of_forall zero_le_one fun x => ?_
  rw [one_mul]
  have hsq : ‖(toLp 2 (P *ᵥ x) : EuclideanSpace ℂ n)‖ ^ 2 ≤
      ‖(toLp 2 x : EuclideanSpace ℂ n)‖ * ‖(toLp 2 (P *ᵥ x) : EuclideanSpace ℂ n)‖ := by
    rw [norm_sq_toLp, ← dotProduct_conjTranspose_mul_self, hP, hPP, ← inner_toLp_toLp]
    exact re_inner_le_norm (𝕜 := ℂ) _ _
  rcases (norm_nonneg (toLp 2 (P *ᵥ x) : EuclideanSpace ℂ n)).lt_or_eq with hpos | hzero
  · rw [sq] at hsq
    exact le_of_mul_le_mul_right hsq hpos
  · rw [← hzero]
    exact norm_nonneg _

namespace IsPVM

variable {A : Type*} [Fintype A] {M : A → Matrix n n ℂ}

theorem norm_le_one (hM : IsPVM M) (a : A) : ‖M a‖ ≤ 1 :=
  norm_le_one_of_isProj (hM.conjTranspose_eq a) (hM.mul_self a)

end IsPVM

end MIPRE.ValueApprox


