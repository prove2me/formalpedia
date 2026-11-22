-- Prove2me | Definitions.Def_Triangular_Auto_TriangularHT
-- name    : Triangular_Auto_TriangularHT
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T18:21:41.359025+00:00
-- url     : https://prove2.me/theorems/f5871d1d-ac4b-4626-a4d5-9d502c891ca5
-- title:
--   Triangular HT
-- statement:
--   Definitions and structural lemmas for Triangular HT, from Joris Roos's pinned The triangular Hilbert transform and Carleson’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Auto/TriangularHT.lean

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
section GaussianCalculus
open Real
def gaussProfile (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)
def gaussProfileD (j : ℕ) : ℝ → ℝ := iteratedDeriv j gaussProfile
lemma contDiff_gaussProfile : ContDiff ℝ ∞ gaussProfile := by
  unfold gaussProfile
  fun_prop
lemma contDiff_gaussProfileD (j : ℕ) : ContDiff ℝ ∞ (gaussProfileD j) := by
  unfold gaussProfileD
  rw [iteratedDeriv_eq_iterate]
  exact contDiff_gaussProfile.iterate_deriv j
lemma differentiable_gaussProfileD (j : ℕ) :
    Differentiable ℝ (gaussProfileD j) := (contDiff_gaussProfileD j).differentiable (by simp)
lemma deriv_gaussProfileD (j : ℕ) : deriv (gaussProfileD j) = gaussProfileD (j + 1) := by
  unfold gaussProfileD
  rw [iteratedDeriv_succ]
lemma hasDerivAt_gaussProfileD (j : ℕ) (x : ℝ) :
    HasDerivAt (gaussProfileD j) (gaussProfileD (j + 1) x) x := by
  rw [← deriv_gaussProfileD]
  exact (differentiable_gaussProfileD j x).hasDerivAt
lemma gaussProfileD_zero : gaussProfileD 0 = gaussProfile := by simp [gaussProfileD]
lemma gaussProfileD_one (x : ℝ) : gaussProfileD 1 x = -x * gaussProfile x := by
  have h : HasDerivAt gaussProfile (-x * gaussProfile x) x := by
    unfold gaussProfile
    have := ((hasDerivAt_pow 2 x).neg.div_const 2).exp
    convert this using 1 <;> simp [Pi.neg_apply] <;> ring
  rw [← h.deriv, ← deriv_gaussProfileD, gaussProfileD_zero]
lemma gaussProfileD_succ_succ (j : ℕ) (x : ℝ) :
    gaussProfileD (j + 2) x = -((j : ℝ) + 1) * gaussProfileD j x - x * gaussProfileD (j + 1) x := by
  induction j generalizing x with
  | zero =>
    have h1 : gaussProfileD 1 = fun x => -x * gaussProfileD 0 x := by
      funext y; rw [gaussProfileD_one, gaussProfileD_zero]
    have : HasDerivAt (fun x => -x * gaussProfileD 0 x) (-1 * gaussProfileD 0 x + -x * gaussProfileD
        1 x) x := (hasDerivAt_id x).neg.mul (hasDerivAt_gaussProfileD 0 x)
    rw [← h1] at this
    rw [← (hasDerivAt_gaussProfileD 1 x).deriv, this.deriv]
    push_cast; ring
  | succ j ih =>
    have h2 : gaussProfileD (j + 2) = fun x =>
        -((j : ℝ) + 1) * gaussProfileD j x - x * gaussProfileD (j + 1) x := funext ih
    have : HasDerivAt (fun x => -((j : ℝ) + 1) * gaussProfileD j x - x * gaussProfileD (j + 1) x)
        (-((j : ℝ) + 1) * gaussProfileD (j + 1) x - (1 * gaussProfileD (j + 1) x + x * gaussProfileD
        (j + 2) x)) x := ((hasDerivAt_gaussProfileD j x).const_mul _).sub ((hasDerivAt_id x).mul
        (hasDerivAt_gaussProfileD (j + 1) x))
    rw [← h2] at this
    rw [← (hasDerivAt_gaussProfileD (j + 2) x).deriv, this.deriv]
    push_cast; ring
lemma gaussProfile_pos (x : ℝ) : 0 < gaussProfile x := Real.exp_pos _
lemma abs_gaussProfileD_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |gaussProfileD j x| ≤ C * (1 + |x|) ^ j * gaussProfile x := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => exact ⟨1, zero_le_one, fun x => by
        simp [gaussProfileD_zero, abs_of_pos (gaussProfile_pos x)]⟩
    | 1, _ => exact ⟨1, zero_le_one, fun x => by
        rw [gaussProfileD_one, abs_mul, abs_neg, abs_of_pos (gaussProfile_pos x)]
        have := gaussProfile_pos x
        nlinarith [abs_nonneg x]⟩
    | j + 2, ih =>
      obtain ⟨C0, hC0, h0⟩ := ih j (by omega)
      obtain ⟨C1, hC1, h1⟩ := ih (j + 1) (by omega)
      refine ⟨((j : ℝ) + 1) * C0 + C1, by positivity, fun x => ?_⟩
      rw [gaussProfileD_succ_succ]
      have hx : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
      have hp := gaussProfile_pos x
      have e0 := h0 x
      have e1 := h1 x
      calc |-((j : ℝ) + 1) * gaussProfileD j x - x * gaussProfileD (j + 1) x|
          ≤ ((j : ℝ) + 1) * |gaussProfileD j x| + |x| * |gaussProfileD (j + 1) x| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
        _ ≤ ((j : ℝ) + 1) * (C0 * (1 + |x|) ^ j * gaussProfile x) + (1 + |x|) * (C1 * (1 + |x|) ^ (j
            + 1) * gaussProfile x) := by
            gcongr
            linarith
        _ ≤ (((j : ℝ) + 1) * C0 + C1) * (1 + |x|) ^ (j + 2) * gaussProfile x := by
            have hpow : (1 + |x|) ^ j ≤ (1 + |x|) ^ (j + 2) :=
              pow_le_pow_right₀ hx (by omega)
            have : (1 + |x|) * (C1 * (1 + |x|) ^ (j + 1) * gaussProfile x) =
                C1 * (1 + |x|) ^ (j + 2) * gaussProfile x := by ring
            rw [this]
            have : ((j : ℝ) + 1) * (C0 * (1 + |x|) ^ j * gaussProfile x) ≤ ((j : ℝ) + 1) * (C0 * (1
                + |x|) ^ (j + 2) * gaussProfile x) := by
              gcongr
            nlinarith
lemma one_add_abs_pow_mul_gaussProfile_le (n : ℕ) (x : ℝ) :
    (1 + |x|) ^ n * gaussProfile x ≤ n.factorial * Real.exp 2 * Real.exp (-(x ^ 2) / 4) := by
  have hy : 0 ≤ 1 + |x| := by positivity
  have h1 : (1 + |x|) ^ n ≤ n.factorial * Real.exp (1 + |x|) := by
    have := Real.pow_div_factorial_le_exp _ hy n
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : Real.exp (1 + |x|) * gaussProfile x ≤ Real.exp 2 * Real.exp (-(x ^ 2) / 4) := by
    unfold gaussProfile
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [sq_nonneg (|x| / 2 - 1)]
  calc (1 + |x|) ^ n * gaussProfile x ≤ n.factorial * Real.exp (1 + |x|) * gaussProfile x := by
        gcongr; exact (gaussProfile_pos x).le
    _ = n.factorial * (Real.exp (1 + |x|) * gaussProfile x) := by ring
    _ ≤ n.factorial * (Real.exp 2 * Real.exp (-(x ^ 2) / 4)) := by gcongr
    _ = _ := by ring
lemma abs_pow_mul_gaussProfileD_le (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |x| ^ m * |gaussProfileD j x| ≤ C * Real.exp (-(x ^ 2) / 4) := by
  obtain ⟨C, hC, h⟩ := abs_gaussProfileD_le j
  refine ⟨C * (m + j).factorial * Real.exp 2, by positivity, fun x => ?_⟩
  have hx : |x| ^ m ≤ (1 + |x|) ^ m := by gcongr; linarith
  calc |x| ^ m * |gaussProfileD j x| ≤ (1 + |x|) ^ m * (C * (1 + |x|) ^ j * gaussProfile x) := by
        gcongr; exact h x
    _ = C * ((1 + |x|) ^ (m + j) * gaussProfile x) := by ring
    _ ≤ C * ((m + j).factorial * Real.exp 2 * Real.exp (-(x ^ 2) / 4)) := by
        exact mul_le_mul_of_nonneg_left (one_add_abs_pow_mul_gaussProfile_le _ x) hC
    _ = _ := by ring
def gaussian (σ t : ℝ) : ℝ := (√(2 * π * σ))⁻¹ * Real.exp (-(t ^ 2) / (2 * σ))
def gaussianD (j : ℕ) (σ : ℝ) : ℝ → ℝ := iteratedDeriv j (gaussian σ)
lemma contDiff_gaussian (σ : ℝ) : ContDiff ℝ ∞ (gaussian σ) := by
  unfold gaussian
  fun_prop
lemma gaussianD_zero (σ : ℝ) : gaussianD 0 σ = gaussian σ := by simp [gaussianD]
lemma hasDerivAt_gaussianD (j : ℕ) (σ t : ℝ) :
    HasDerivAt (gaussianD j σ) (gaussianD (j + 1) σ t) t := by
  have hd : Differentiable ℝ (gaussianD j σ) := (contDiff_gaussian σ).differentiable_iteratedDeriv j
      (by exact_mod_cast WithTop.coe_lt_top _)
  have : deriv (gaussianD j σ) = gaussianD (j + 1) σ := by
    unfold gaussianD; rw [iteratedDeriv_succ]
  rw [← this]
  exact (hd t).hasDerivAt
lemma continuous_gaussianD (j : ℕ) (σ : ℝ) : Continuous (gaussianD j σ) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_gaussianD j σ t).continuousAt
lemma gaussian_eq_profile {σ : ℝ} (hσ : 0 < σ) :
    gaussian σ = fun t => (√(2 * π))⁻¹ * (√σ)⁻¹ * gaussProfile ((√σ)⁻¹ * t) := by
  funext t
  unfold gaussian gaussProfile
  have hs : 0 < √σ := Real.sqrt_pos.2 hσ
  rw [show (2 * π * σ) = (2 * π) * σ by ring, Real.sqrt_mul (by positivity), mul_inv]
  congr 2
  rw [mul_pow, inv_pow, Real.sq_sqrt hσ.le]
  field_simp
lemma gaussianD_eq_profile (j : ℕ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    gaussianD j σ t = (√(2 * π))⁻¹ * (√σ)⁻¹ ^ (j + 1) * gaussProfileD j ((√σ)⁻¹ * t) := by
  unfold gaussianD
  rw [gaussian_eq_profile hσ]
  have hcd : ContDiff ℝ j (fun t => gaussProfile ((√σ)⁻¹ * t)) := (contDiff_gaussProfile.of_le (by
      exact_mod_cast le_top)).comp (by fun_prop)
  rw [iteratedDeriv_const_mul (f := fun t => gaussProfile ((√σ)⁻¹ * t)) _ hcd.contDiffAt]
  rw [iteratedDeriv_comp_const_mul (contDiff_gaussProfile.of_le (by exact_mod_cast le_top))
      ((√σ)⁻¹)]
  simp only [gaussProfileD]
  ring
theorem integral_gaussian_eq_one {σ : ℝ} (hσ : 0 < σ) : ∫ t, gaussian σ t = 1 := by
  unfold gaussian
  rw [integral_const_mul]
  have : (fun t : ℝ => Real.exp (-(t ^ 2) / (2 * σ))) =
      fun t => Real.exp (-(1 / (2 * σ)) * t ^ 2) := by
    funext t; congr 1; ring
  rw [this, integral_gaussian, div_div_eq_mul_div, div_one]
  rw [show (π * (2 * σ)) = 2 * π * σ by ring]
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne'
theorem abs_pow_mul_gaussianD_le (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 0 < σ → ∀ t : ℝ, |t| ^ m * |gaussianD j σ t| ≤ C * (√σ) ^ m *
      (√σ)⁻¹ ^ (j + 1) * Real.exp (-(t ^ 2) / (4 * σ)) := by
  obtain ⟨C, hC, h⟩ := abs_pow_mul_gaussProfileD_le j m
  refine ⟨(√(2 * π))⁻¹ * C, by positivity, fun σ hσ t => ?_⟩
  have hs : 0 < √σ := Real.sqrt_pos.2 hσ
  set x := (√σ)⁻¹ * t with hx
  have ht : t = √σ * x := by rw [hx]; field_simp
  have hx2 : -(x ^ 2) / 4 = -(t ^ 2) / (4 * σ) := by
    simp only [hx]; rw [mul_pow, inv_pow, Real.sq_sqrt hσ.le]; field_simp
  rw [gaussianD_eq_profile j hσ, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < (√(2 * π))⁻¹),
    abs_of_pos (by positivity : (0:ℝ) < (√σ)⁻¹ ^ (j + 1)), ← hx, ← hx2]
  have hxt : |t| ^ m = (√σ) ^ m * |x| ^ m := by
    rw [ht, abs_mul, abs_of_pos hs, mul_pow]
  rw [hxt]
  have := h x
  calc (√σ) ^ m * |x| ^ m * ((√(2 * π))⁻¹ * (√σ)⁻¹ ^ (j + 1) * |gaussProfileD j x|)
      = (√(2 * π))⁻¹ * (√σ) ^ m * (√σ)⁻¹ ^ (j + 1) * (|x| ^ m * |gaussProfileD j x|) := by ring
    _ ≤ (√(2 * π))⁻¹ * (√σ) ^ m * (√σ)⁻¹ ^ (j + 1) * (C * Real.exp (-(x ^ 2) / 4)) := by
        gcongr
    _ = _ := by ring
lemma integrable_exp_neg_sq_div {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t : ℝ => Real.exp (-(t ^ 2) / (4 * σ))) := by
  have : (fun t : ℝ => Real.exp (-(t ^ 2) / (4 * σ))) =
      fun t => Real.exp (-(1 / (4 * σ)) * t ^ 2) := by
    funext t; congr 1; ring
  rw [this]
  exact integrable_exp_neg_mul_sq (by positivity)
theorem integrable_pow_mul_gaussianD (j m : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun t => t ^ m * gaussianD j σ t) := by
  obtain ⟨C, hC, h⟩ := abs_pow_mul_gaussianD_le j m
  refine ((integrable_exp_neg_sq_div hσ).const_mul (C * (√σ) ^ m * (√σ)⁻¹ ^ (j + 1))).mono'
      ((continuous_pow m).mul (continuous_gaussianD j σ)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact h σ hσ t
theorem integrable_gaussianD (j : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (gaussianD j σ) := by
  simpa using integrable_pow_mul_gaussianD j 0 hσ
end GaussianCalculus
section LatticeApproximation
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
def latticeFloor (N : ℕ) (x : Fin d → ℝ) : Fin d → ℝ := fun i => (⌊(N : ℝ) * x i⌋ : ℝ) / N
def latticeCube (N : ℕ) (k : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico ((k i : ℝ) / N) (((k i : ℝ) + 1) / N)
end LatticeApproximation
end
end Auto
@[expose] public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
namespace Auto
noncomputable section
section HilbertSchmidt
variable {m n : Type*} [Fintype m] [Fintype n]
def hsSq (R : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, ‖R i j‖ ^ 2
def hsRe (X Y : Matrix m n ℂ) : ℝ := ((Xᴴ * Y).trace).re
lemma hsSq_nonneg (R : Matrix m n ℂ) : 0 ≤ hsSq R := by unfold hsSq; positivity
lemma hsRe_eq_sum (X Y : Matrix m n ℂ) :
    hsRe X Y = ∑ i, ∑ j, ((starRingEnd ℂ) (X i j) * Y i j).re := by
  simp only [hsRe, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, RCLike.star_def]
  rw [Finset.sum_comm]
lemma hsRe_self (X : Matrix m n ℂ) : hsRe X X = hsSq X := by
  rw [hsRe_eq_sum, hsSq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast
lemma re_trace_conjTranspose_mul_self (X : Matrix m n ℂ) : ((Xᴴ * X).trace).re = hsSq X :=
  hsRe_self X
lemma hsRe_comm (X Y : Matrix m n ℂ) : hsRe X Y = hsRe Y X := by
  rw [hsRe_eq_sum, hsRe_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_re ((starRingEnd ℂ) (X i j) * Y i j)]
  simp [mul_comm]
lemma hsRe_add_right (X Y Z : Matrix m n ℂ) :
    hsRe X (Y + Z) = hsRe X Y + hsRe X Z := by
  simp [hsRe, Matrix.mul_add, Matrix.trace_add]
lemma abs_hsRe_le (X Y : Matrix m n ℂ) : |hsRe X Y| ≤ √(hsSq X) * √(hsSq Y) := by
  rw [hsRe_eq_sum]
  have h1 : |∑ i, ∑ j, ((starRingEnd ℂ) (X i j) * Y i j).re| ≤ ∑ i, ∑ j, ‖X i j‖ * ‖Y i j‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (Complex.abs_re_le_norm _).trans ?_
    simp
  refine h1.trans ?_
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (m × n)) (fun p => ‖X p.1 p.2‖) (fun p
      => ‖Y p.1 p.2‖)
  simp only [Fintype.sum_prod_type] at this
  exact this
end HilbertSchmidt
section PositiveMatrices
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [Fintype m] [DecidableEq m] [DecidableEq n] in
lemma re_trace_nonneg_of_posSemidef {P : Matrix n n ℂ} (hP : P.PosSemidef) : 0 ≤ (P.trace).re := by
  have := hP.trace_nonneg
  exact (Complex.nonneg_iff.1 this).1
omit [DecidableEq m] in
lemma re_trace_conj_mul_mul_ge {B : Matrix n n ℂ} {β : ℝ}
    (hB : (B - (β : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Z : Matrix n m ℂ) :
    β * hsSq Z ≤ ((Zᴴ * B * Z).trace).re := by
  have h := re_trace_nonneg_of_posSemidef (hB.conjTranspose_mul_mul_same Z)
  have e : Zᴴ * (B - (β : ℂ) • 1) * Z = Zᴴ * B * Z - (β : ℂ) • (Zᴴ * Z) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [e, Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    re_trace_conjTranspose_mul_self] at h
  linarith
lemma sylvester_lower {B : Matrix n n ℂ} {A : Matrix m m ℂ} {α β : ℝ}
    (hB : (B - (β : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hA : (A - (α : ℂ) • (1 : Matrix m m ℂ)).PosSemidef) (Z : Matrix n m ℂ) :
    (α + β) * hsSq Z ≤ hsRe Z (B * Z + Z * A) := by
  rw [hsRe_add_right]
  have h1 : β * hsSq Z ≤ hsRe Z (B * Z) := by
    have := re_trace_conj_mul_mul_ge hB Z
    rwa [Matrix.mul_assoc] at this
  have h2 : α * hsSq Z ≤ hsRe Z (Z * A) := by
    have := re_trace_conj_mul_mul_ge hA Zᴴ
    rw [Matrix.conjTranspose_conjTranspose] at this
    have e : (Z * A * Zᴴ).trace = (Zᴴ * (Z * A)).trace := by
      rw [Matrix.trace_mul_comm]
    rw [e] at this
    have hs : hsSq Zᴴ = hsSq Z := by
      unfold hsSq; rw [Finset.sum_comm]; simp [Matrix.conjTranspose_apply]
    rw [hs] at this
    exact this
  linarith
omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_mul_le {k : Type*} [Fintype k] (X : Matrix m n ℂ) (Y : Matrix n k ℂ) :
    hsSq (X * Y) ≤ hsSq X * hsSq Y := by
  unfold hsSq
  have key : ∀ i j, ‖(X * Y) i j‖ ^ 2 ≤ (∑ l, ‖X i l‖ ^ 2) * (∑ l, ‖Y l j‖ ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
    simp only [norm_mul]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖X i l‖) (fun l => ‖Y l j‖)
  calc ∑ i, ∑ j, ‖(X * Y) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ l, ‖X i l‖ ^ 2) * (∑ l, ‖Y l j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ l, ‖X i l‖ ^ 2) * ∑ j, ∑ l, ‖Y l j‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm (f := fun j l => ‖Y l j‖ ^ 2)]
end PositiveMatrices
section SpectralEnergy
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def trF (f : ℝ → ℝ) (P : Matrix n n ℂ) : ℝ := ((cfc f P).trace).re
def energy (P : Matrix n n ℂ) : ℝ := trF (fun x => x ^ (3 / 2 : ℝ)) P
def energyReg (η : ℝ) (P : Matrix n n ℂ) : ℝ :=
  trF (fun x => (x + η) ^ (3 / 2 : ℝ) - η ^ (3 / 2 : ℝ)) P
omit [Fintype m] [DecidableEq m] in
def costInt (A K X : Matrix n n ℂ) : ℝ := 2 * hsRe K X - (hsRe X (A * X) + hsRe X (X * A))
def matCost (P K : Matrix n n ℂ) : ℝ≥0∞ :=
  ⨆ X : Matrix n n ℂ, ENNReal.ofReal ((3 / 2) * costInt (CFC.sqrt P) K X)
def eigCoord {P : Matrix n n ℂ} (hP : P.IsHermitian) (K : Matrix n n ℂ) : Matrix n n ℂ :=
  star (hP.eigenvectorUnitary : Matrix n n ℂ) * K * (hP.eigenvectorUnitary : Matrix n n ℂ)
def matCostBil (P K L : Matrix n n ℂ) :
    ℝ := ((matCost P (K + L)).toReal - (matCost P (K - L)).toReal) / 4
omit [Fintype m] [DecidableEq m] [DecidableEq n] in
lemma hsSq_eq_zero_iff (Z : Matrix n n ℂ) : hsSq Z = 0 ↔ Z = 0 := by
  constructor
  · intro h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
      fun j _ => sq_nonneg ‖Z i j‖)).1 h
    ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖Z i j‖)).1 (h' i
        (Finset.mem_univ i)) j (Finset.mem_univ j)
    simpa using this
  · rintro rfl; simp [hsSq]
omit [Fintype m] [DecidableEq m] in
lemma sqrt_hsSq_le_sylvester {B A : Matrix n n ℂ} {α β : ℝ} (hαβ : 0 < α + β)
    (hB : (B - (β : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hA : (A - (α : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Z : Matrix n n ℂ) :
    √(hsSq Z) ≤ √(hsSq (B * Z + Z * A)) / (α + β) := by
  have h1 := sylvester_lower hB hA Z
  have h2 := (le_abs_self _).trans (abs_hsRe_le Z (B * Z + Z * A))
  rw [le_div_iff₀ hαβ]
  rcases (hsSq_nonneg Z).eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, zero_mul]; exact Real.sqrt_nonneg _
  · have hs : 0 < √(hsSq Z) := Real.sqrt_pos.2 hpos
    have : (α + β) * (√(hsSq Z) * √(hsSq Z)) ≤ √(hsSq Z) * √(hsSq (B * Z + Z * A)) := by
      rw [Real.mul_self_sqrt (hsSq_nonneg Z)]; linarith
    nlinarith
open Classical in

def sylvSol (A Y : Matrix n n ℂ) : Matrix n n ℂ :=
  if h : ∃ X, A * X + X * A = Y then h.choose else 0
omit [Fintype m] [DecidableEq m] in
theorem sylvSol_spec {A : Matrix n n ℂ} {α : ℝ} (hα : 0 < α)
    (hA : (A - (α : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Y : Matrix n n ℂ) :
    A * sylvSol A Y + sylvSol A Y * A = Y ∧ ∀ X, A * X + X * A = Y → X = sylvSol A Y := by
  let L : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun X => A * X + X * A
      map_add' := fun X Z => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c X => by simp [smul_add] }
  have hinj : Function.Injective L := by
    intro X Z hXZ
    have h0 : A * (X - Z) + (X - Z) * A = 0 := by
      have : A * X + X * A = A * Z + Z * A := hXZ
      rw [Matrix.mul_sub, Matrix.sub_mul]
      rw [show A * X - A * Z + (X * A - Z * A) = (A * X + X * A) - (A * Z + Z * A) by abel,
        this, sub_self]
    have := sqrt_hsSq_le_sylvester (by linarith : 0 < α + α) hA hA (X - Z)
    rw [h0] at this
    simp only [hsSq, Matrix.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero, zero_div] at this
    have h2 : hsSq (X - Z) = 0 := by
      have := Real.sqrt_eq_zero'.1 (le_antisymm this (Real.sqrt_nonneg _))
      exact le_antisymm this (hsSq_nonneg _)
    exact sub_eq_zero.1 ((hsSq_eq_zero_iff _).1 h2)
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.1 hinj
  have hex : ∃ X, A * X + X * A = Y := hsurj Y
  have hspec : A * sylvSol A Y + sylvSol A Y * A = Y := by
    rw [sylvSol, dif_pos hex]; exact hex.choose_spec
  refine ⟨hspec, fun X hX => hinj ?_⟩
  change A * X + X * A = A * sylvSol A Y + sylvSol A Y * A
  rw [hX, hspec]
end SpectralEnergy
section EnergyRegularization
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n] in
lemma tendsto_hsSq_sub {α : Type*} {l : Filter α} {f : α → Matrix n n ℂ} {g : Matrix n n ℂ}
    (h : ∀ i j, Tendsto (fun a => f a i j) l (𝓝 (g i j))) :
    Tendsto (fun a => hsSq (f a - g)) l (𝓝 0) := by
  have : (0 : ℝ) = ∑ i : n, ∑ j : n, ‖(0 : ℂ)‖ ^ 2 := by simp
  rw [this]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  refine ((continuous_norm.tendsto _).comp ?_).pow 2
  have := (h i j).sub (tendsto_const_nhds (x := g i j))
  simpa using this
omit [DecidableEq n] in
lemma norm_entry_le_sqrt_hsSq (Z : Matrix n n ℂ) (i j : n) : ‖Z i j‖ ≤ √(hsSq Z) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold hsSq
  refine (Finset.single_le_sum (f := fun j => ‖Z i j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ
      j)).trans ?_
  exact Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖ ^ 2) (fun i _ => Finset.sum_nonneg fun j _
      => sq_nonneg _) (Finset.mem_univ i)
end EnergyRegularization
local instance _p2m_local_instance_5846efa9ac_1611 {n : Type*} : MeasurableSpace (Matrix n n ℂ) := borel _
local instance _p2m_local_instance_5846efa9ac_1612 {n : Type*} : BorelSpace (Matrix n n ℂ) := ⟨rfl⟩
section SylvesterCost
variable {n : Type*} [Fintype n] [DecidableEq n] {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
def matIntegral (ν : Measure Z) (M : Z → Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∫ z, M z i j ∂ν
end SylvesterCost
section CostProps
variable {n : Type*} [Fintype n] [DecidableEq n]
end CostProps
section CyclicTraceCore
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
end CyclicTraceCore
section ThreeBlocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def blk3 (X : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ :=
  Matrix.comp _ _ _ _ _ X
def emb2 (p r : Fin 3) : Matrix (Fin 3 × ι) (ι ⊕ ι) ℂ :=
  Matrix.of fun x s => Sum.elim (fun b => if x = (p, b) then (1 : ℂ) else 0) (fun b => if x = (r, b)
      then (1 : ℂ) else 0) s
def emb1 (p : Fin 3) : Matrix (Fin 3 × ι) ι ℂ :=
  Matrix.of fun x b => if x = (p, b) then (1 : ℂ) else 0
end ThreeBlocks
section CyclicTrace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def rowMat (W V : Matrix ι ι ℂ) : Matrix ι (ι ⊕ ι) ℂ := Matrix.fromCols W Vᴴ
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
def cycMb : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![0, W0, W2ᴴ; W0ᴴ, 0, W1; W2, W1ᴴ, 0]
def cycDb : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![D0, 0, 0; 0, D1, 0; 0, 0, D2]
def cycP0 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![1, 0, 0; 0, 0, 0; 0, 0, 0]
def cycP1 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![0, 0, 0; 0, 1, 0; 0, 0, 0]
def cycP2 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ) := !![0, 0, 0; 0, 0, 0; 0, 0, 1]
end CyclicTrace
end
end Auto
@[expose] public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
namespace Auto
noncomputable section
section GramWeight
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
def rdiag (f : ι → ℝ) : Matrix ι ι ℂ := diagonal fun i => ((f i : ℝ) : ℂ)
def wGram (B : Matrix ι κ ℂ) (f : ι → ℝ) : Matrix κ κ ℂ := Bᴴ * rdiag f * B
def gweight (u : ι → ℝ) (h σ p : ℝ) : ι → ℝ := fun i => h * gaussian σ (u i - p)
end GramWeight
section HeatMatrices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
structure HeatData (ι : Type*) where
  u : ι → ℝ
  h : ℝ
  A : Fin 3 → Matrix ι ι ℂ
namespace HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
def w (v : Fin 3) : ι → ℝ := gweight Hd.u Hd.h (σ v) (p v)
def sqw (v : Fin 3) : ι → ℝ := fun i => √(Hd.w p σ v i)
def W (v : Fin 3) : Matrix ι ι ℂ := rdiag (Hd.sqw p σ v) * Hd.A v * rdiag (Hd.sqw p σ (v + 1))
def R (v : Fin 3) : Matrix ι (ι ⊕ ι) ℂ := rowMat (Hd.W p σ v) (Hd.W p σ (v - 1))
def T (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (Hd.R p σ v)ᴴ * Hd.R p σ v
def S (v : Fin 3) : Matrix ι ι ℂ := Hd.R p σ v * (Hd.R p σ v)ᴴ
def e (η : ℝ) (v : Fin 3) : ℝ := energyReg η (Hd.T p σ v)
def Dc (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  Matrix.fromBlocks (rdiag (Hd.sqw p σ (v + 1))) 0 0 (rdiag (Hd.sqw p σ (v - 1)))
def Brow (v : Fin 3) : Matrix ι (ι ⊕ ι) ℂ := rowMat (Hd.A v) (Hd.A (v - 1)) * Hd.Dc p σ v
def Bnext (v : Fin 3) : Matrix ι ι ℂ := (Hd.A v)ᴴ * rdiag (Hd.sqw p σ v)
def Bprev (v : Fin 3) : Matrix ι ι ℂ := Hd.A (v - 1) * rdiag (Hd.sqw p σ v)
def dw (v : Fin 3) : ι → ℝ := fun i => -(Hd.h * gaussianD 1 (σ v) (Hd.u i - p v))
def ddw (v : Fin 3) : ι → ℝ := fun i => Hd.h * gaussianD 2 (σ v) (Hd.u i - p v)
def Ui (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := wGram (Hd.Brow p σ v) (Hd.dw p σ v)
def Pnext (v : Fin 3) : Matrix ι ι ℂ := wGram (Hd.Bnext p σ v) (Hd.dw p σ (v + 1))
def Pprev (v : Fin 3) : Matrix ι ι ℂ := wGram (Hd.Bprev p σ v) (Hd.dw p σ (v - 1))
def V (η : ℝ) (v : Fin 3) : ℝ := (matCost (Hd.T p σ v + (η : ℂ) • 1) (Hd.Ui p σ v)).toReal
def Ynext (η : ℝ) (v : Fin 3) : ℝ := (matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pnext p σ v)).toReal
def Yprev (η : ℝ) (v : Fin 3) : ℝ := (matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pprev p σ v)).toReal
def Z (η : ℝ) (v : Fin 3) : ℝ :=
  matCostBil (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pnext p σ v) (Hd.Pprev p σ v)
def tr32 (η : ℝ) {κ : Type*} [Fintype κ] [DecidableEq κ] (Γ K : Matrix κ κ ℂ) :
    ℝ := (3 / 2) * ((CFC.sqrt (Γ + (η : ℂ) • 1) * K).trace).re
end HeatData
end HeatMatrices
section BlockCost
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def ein1 : Matrix (ι ⊕ ι) ι ℂ := Matrix.fromRows 1 0
def ein2 : Matrix (ι ⊕ ι) ι ℂ := Matrix.fromRows 0 1
end BlockCost
section Neighbor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
def N (v : Fin 3) : Matrix ι ι ℂ := rdiag (fun i => Hd.dw p σ v i / Hd.w p σ v i)
end HeatData
namespace HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
end HeatData
end Neighbor
section VarianceDerivatives
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
def dv (v : Fin 3) : ι ⊕ ι → ℝ := Sum.elim (Hd.sqw p σ (v + 1)) (Hd.sqw p σ (v - 1))
def X (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := wGram (rowMat (Hd.A v) (Hd.A (v - 1))) (Hd.w p σ v)
def dsq (k : Fin 3) (i : ι) : ℝ := (Hd.ddw p σ k i / 2) / (2 * Hd.sqw p σ k i)
def Mrow (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := wGram (Hd.Brow p σ v) (fun i => Hd.ddw p σ v
    i / 2)
def Mnext (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  rdiag (Sum.elim (Hd.dsq p σ (v + 1)) 0) * Hd.X p σ v * rdiag (Hd.dv p σ v) +
    rdiag (Hd.dv p σ v) * Hd.X p σ v * rdiag (Sum.elim (Hd.dsq p σ (v + 1)) 0)
def Mprev (v : Fin 3) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  rdiag (Sum.elim 0 (Hd.dsq p σ (v - 1))) * Hd.X p σ v * rdiag (Hd.dv p σ v) +
    rdiag (Hd.dv p σ v) * Hd.X p σ v * rdiag (Sum.elim 0 (Hd.dsq p σ (v - 1)))
end HeatData
end VarianceDerivatives
section MatContinuity
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n] in
lemma sqrt_hsSq_add_le (X Y : Matrix n n ℂ) : √(hsSq (X + Y)) ≤ √(hsSq X) + √(hsSq Y) := by
  have h1 : hsSq (X + Y) = hsSq X + hsSq Y + 2 * hsRe X Y := by
    rw [← hsRe_self, ← hsRe_self, ← hsRe_self, hsRe_add_right, hsRe_comm (X + Y) X,
      hsRe_comm (X + Y) Y, hsRe_add_right, hsRe_add_right, hsRe_comm Y X]; ring
  have h2 := (le_abs_self _).trans (abs_hsRe_le X Y)
  rw [Real.sqrt_le_left (by positivity), h1]
  have hX := Real.sq_sqrt (hsSq_nonneg X)
  have hY := Real.sq_sqrt (hsSq_nonneg Y)
  nlinarith
omit [DecidableEq n] in
lemma sqrt_hsSq_neg (X : Matrix n n ℂ) : hsSq (-X) = hsSq X := by simp [hsSq]
omit [DecidableEq n] in
lemma sqrt_hsSq_mul_le (X Y : Matrix n n ℂ) : √(hsSq (X * Y)) ≤ √(hsSq X) * √(hsSq Y) := by
  classical
  rw [← Real.sqrt_mul (hsSq_nonneg X)]
  exact Real.sqrt_le_sqrt (hsSq_mul_le X Y)
lemma sqrt_hsSq_sylvSol_le {A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (hA : (A - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Y : Matrix n n ℂ) :
    √(hsSq (sylvSol A Y)) ≤ √(hsSq Y) / (c + c) := by
  have := sqrt_hsSq_le_sylvester (by positivity : 0 < c + c) hA hA (sylvSol A Y)
  rwa [(sylvSol_spec hc hA Y).1] at this
lemma sqrt_hsSq_sylvSol_sub_le {A₁ A₂ : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (h₁ : (A₁ - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (h₂ : (A₂ - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) (Y₁ Y₂ : Matrix n n ℂ) :
    √(hsSq (sylvSol A₁ Y₁ - sylvSol A₂ Y₂)) ≤ (√(hsSq (Y₁ - Y₂)) + 2 * (√(hsSq (A₁ - A₂)) *
      (√(hsSq Y₂) / (c + c)))) / (c + c) := by
  set X₁ := sylvSol A₁ Y₁
  set X₂ := sylvSol A₂ Y₂
  have s₁ := (sylvSol_spec hc h₁ Y₁).1
  have s₂ := (sylvSol_spec hc h₂ Y₂).1
  have e : A₁ * (X₁ - X₂) + (X₁ - X₂) * A₁ = (Y₁ - Y₂) + -((A₁ - A₂) * X₂) + -(X₂ * (A₁ - A₂)) := by
    rw [← s₁, ← s₂]; noncomm_ring
  have h := sqrt_hsSq_le_sylvester (by positivity : 0 < c + c) h₁ h₁ (X₁ - X₂)
  rw [e] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have hX₂ := sqrt_hsSq_sylvSol_le hc h₂ Y₂
  refine (sqrt_hsSq_add_le _ _).trans ?_
  have t1 := sqrt_hsSq_add_le (Y₁ - Y₂) (-((A₁ - A₂) * X₂))
  rw [sqrt_hsSq_neg] at t1 ⊢
  have t2 := sqrt_hsSq_mul_le (A₁ - A₂) X₂
  have t3 := sqrt_hsSq_mul_le X₂ (A₁ - A₂)
  have hA0 := Real.sqrt_nonneg (hsSq (A₁ - A₂))
  have : √(hsSq (A₁ - A₂)) * √(hsSq X₂) ≤ √(hsSq (A₁ - A₂)) * (√(hsSq Y₂) / (c + c)) :=
    mul_le_mul_of_nonneg_left hX₂ hA0
  nlinarith [Real.sqrt_nonneg (hsSq X₂)]
omit [DecidableEq n] in
lemma tendsto_entry_of_hsSq {α : Type*} {l : Filter α} {f : α → Matrix n n ℂ} {g : Matrix n n ℂ}
    (h : Tendsto (fun a => √(hsSq (f a - g))) l (𝓝 0)) :
    Tendsto f l (𝓝 g) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun a => ?_) h
  have := norm_entry_le_sqrt_hsSq (f a - g) i j
  simpa using this
omit [DecidableEq n] in
lemma tendsto_sqrt_hsSq_sub {α : Type*} {l : Filter α} {f : α → Matrix n n ℂ} {g : Matrix n n ℂ}
    (h : Tendsto f l (𝓝 g)) :
    Tendsto (fun a => √(hsSq (f a - g))) l (𝓝 0) := by
  have := tendsto_hsSq_sub (f := f) (g := g) fun i j =>
    tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h i) j
  simpa using this.sqrt
lemma ContinuousOn.sylvSol {Z : Type*} [TopologicalSpace Z] {A Y : Z → Matrix n n ℂ} {s : Set Z}
    (hA : ContinuousOn A s) (hY : ContinuousOn Y s) {c : ℝ} (hc : 0 < c)
    (hpos : ∀ z ∈ s, (A z - (c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    ContinuousOn (fun z => sylvSol (A z) (Y z)) s := by
  intro z hz
  refine tendsto_entry_of_hsSq ?_
  have hA0 := tendsto_sqrt_hsSq_sub (hA z hz)
  have hY0 := tendsto_sqrt_hsSq_sub (hY z hz)
  have h1 : Tendsto (fun a => (√(hsSq (Y a - Y z)) + 2 * (√(hsSq (A a - A z)) * (√(hsSq (Y z)) / (c
      + c)))) / (c + c)) (𝓝[s] z) (𝓝 0) := by
    have := ((hY0.add ((hA0.mul_const (√(hsSq (Y z)) / (c + c))).const_mul 2)).div_const (c + c))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => Real.sqrt_nonneg _) ?_ h1
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact sqrt_hsSq_sylvSol_sub_le hc (hpos a ha) (hpos z hz) _ _
end MatContinuity
section CoordIBP
end CoordIBP
section GaussBounds
def edec (b x : ℝ) : ℝ := Real.exp (-(x ^ 2) / (16 * b))
end GaussBounds
section HeatBounds
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
def MA : ℝ := ∑ k, ∑ i, ∑ j, ‖Hd.A k i j‖
def phi (b : ℝ) (v : Fin 3) (p : Fin 3 → ℝ) : ℝ :=
  edec b (p v) * (edec b (p (v + 1)) + edec b (p (v - 1)))
end HeatData
end HeatBounds
section EntryBounds
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end EntryBounds
section MatBounds
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
end MatBounds
section EnergyBounds
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end EnergyBounds
section HeatContinuity
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
namespace HeatData
variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}
end HeatData
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
namespace HeatData
variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}
end HeatData
end HeatContinuity
section GaussianCenterIntegration
def Gm (β : ℝ) (m : ℕ) (s : ℝ) (p : Fin 3 → ℝ) : ℝ := gaussianD m (β * s) (p 0 + p 1 + p 2)
def gdom (ε : ℝ) (p : Fin 3 → ℝ) : ℝ := ∏ k, Real.exp (-ε * p k ^ 2)
end GaussianCenterIntegration
section DifferentiationUnderIntegral
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι) (α : Fin 3 → ℝ)
def sig (s : ℝ) : Fin 3 → ℝ := fun k => α k * s
end HeatData
end DifferentiationUnderIntegral
section VertexEnergies
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ) (v : Fin 3)
def qE (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.e p (sig α s) η v
def qDr (s : ℝ) (p : Fin 3 → ℝ) : ℝ := tr32 η (Hd.T p (sig α s) v) (Hd.Ui p (sig α s) v)
def qDn (s : ℝ) (p : Fin 3 → ℝ) : ℝ := tr32 η (Hd.S p (sig α s) v) (Hd.Pnext p (sig α s) v)
def qDp (s : ℝ) (p : Fin 3 → ℝ) : ℝ := tr32 η (Hd.S p (sig α s) v) (Hd.Pprev p (sig α s) v)
def qA (s : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  tr32 η (Hd.T p (sig α s) v) (wGram (Hd.Brow p (sig α s) v) (Hd.ddw p (sig α s) v))
def qB (s : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  tr32 η (Hd.S p (sig α s) v) (wGram (Hd.Bnext p (sig α s) v) (Hd.ddw p (sig α s) (v + 1)))
def qC (s : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  tr32 η (Hd.S p (sig α s) v) (wGram (Hd.Bprev p (sig α s) v) (Hd.ddw p (sig α s) (v - 1)))
def qV (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.V p (sig α s) η v
def qYn (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.Ynext p (sig α s) η v
def qYp (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.Yprev p (sig α s) η v
def qZ (s : ℝ) (p : Fin 3 → ℝ) : ℝ := Hd.Z p (sig α s) η v
end HeatData
end VertexEnergies
section VertexIdentities
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ) (v : Fin 3)
end HeatData
end VertexIdentities
section NeighborAbsorption
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end NeighborAbsorption
section IntegratedDissipation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ)
def Jbar (s : ℝ) : ℝ := ∫ p, Gm (1 / 10) 0 s p * ∑ v, Hd.qE α η v s p
def Vbar (v : Fin 3) (s : ℝ) : ℝ := ∫ p, Gm (1 / 10) 0 s p * Hd.qV α η v s p
end HeatData
end IntegratedDissipation
section LatticeGaussianWeights
lemma gaussian_nonneg' (σ t : ℝ) : 0 ≤ gaussian σ t := by unfold gaussian; positivity
end LatticeGaussianWeights
section LatticeGaussianSums
lemma integrable_gaussian' {σ : ℝ} (hσ : 0 < σ) : Integrable (gaussian σ) := by
  have := integrable_gaussianD 0 hσ
  rwa [gaussianD_zero] at this
end LatticeGaussianSums
section PlaneIntegral
end PlaneIntegral
section InitialEnergy
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
def nCube (v : Fin 3) : ℝ := Hd.h ^ 2 * ∑ i, ∑ j, ‖Hd.A v i j‖ ^ 3
end HeatData
end InitialEnergy
section InitialEnergyBound
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end InitialEnergyBound
end
end Auto
@[expose] public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
namespace Auto
noncomputable section
section GaussianPlane
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end GaussianPlane
section EnergyIntegrability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι) {kk : ι → ℤ}
end HeatData
end EnergyIntegrability
section MatrixNorm
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {kk : ι → ℤ}
def nNorm (h : ℝ) (A : Matrix ι ι ℂ) : ℝ := (h ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 3) ^ (1 / 3 : ℝ)
end MatrixNorm
section RegularizationLimit
variable {n : Type*} [Fintype n] [DecidableEq n]
end RegularizationLimit
section EnergyNonnegativity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end EnergyNonnegativity
section IntegratedRegularization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end IntegratedRegularization
section CostDensity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
def costDensity (α : Fin 3 → ℝ) (η : ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  Gm (1 / 10) 0 z.1 z.2 * ∑ v, Hd.qV α η v z.1 z.2
end HeatData
end CostDensity
section GaussianComparison
lemma poly_exp_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, (1 + |y|) ^ d * Real.exp (-ε * y ^ 2) ≤ B := by
  set K := max 1 (√(2 * ε))⁻¹
  have hK : 1 ≤ K := le_max_left _ _
  have hs : 0 < √(2 * ε) := Real.sqrt_pos.2 (by positivity)
  refine ⟨K ^ d * (d.factorial * Real.exp 2), by positivity, fun y => ?_⟩
  set z := √(2 * ε) * y
  have hzy : 1 + |y| ≤ K * (1 + |z|) := by
    have : |y| = (√(2 * ε))⁻¹ * |z| := by
      rw [abs_mul, abs_of_pos hs, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    rw [this]
    have h1 : (√(2 * ε))⁻¹ ≤ K := le_max_right _ _
    nlinarith [abs_nonneg z]
  have hez : Real.exp (-ε * y ^ 2) = gaussProfile z := by
    unfold gaussProfile; congr 1
    simp only [z]; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hez]
  calc (1 + |y|) ^ d * gaussProfile z ≤ (K * (1 + |z|)) ^ d * gaussProfile z :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzy d)
          (gaussProfile_pos z).le
    _ = K ^ d * ((1 + |z|) ^ d * gaussProfile z) := by rw [mul_pow]; ring
    _ ≤ K ^ d * (d.factorial * Real.exp 2 * Real.exp (-(z ^ 2) / 4)) :=
        mul_le_mul_of_nonneg_left (one_add_abs_pow_mul_gaussProfile_le d z) (by positivity)
    _ ≤ K ^ d * (d.factorial * Real.exp 2 * 1) := by
        gcongr; rw [Real.exp_le_one_iff]; have := sq_nonneg z; linarith
    _ = _ := by ring
theorem gaussianD_ratio_le (d : ℕ) {q l : ℝ} (hq : 0 < q) (hql : q < l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ x : ℝ, √s ^ d * |gaussianD d (q * s) x| ≤ C * gaussian
      (l * s) x := by
  have hl : 0 < l := hq.trans hql
  obtain ⟨C0, hC0, hprof⟩ := abs_gaussProfileD_le d
  set ε := (1 - q / l) / 2
  have hε : 0 < ε := by
    have : q / l < 1 := (div_lt_one hl).2 hql
    simp only [ε]; linarith
  obtain ⟨B, hB0, hB⟩ := poly_exp_bound d hε
  have hsq : 0 < √q := Real.sqrt_pos.2 hq
  have hsl : 0 < √l := Real.sqrt_pos.2 hl
  refine ⟨(√q)⁻¹ ^ (d + 1) * C0 * B * √l, by positivity, fun s hs x => ?_⟩
  have hss : 0 < √s := Real.sqrt_pos.2 hs
  have h2π : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)
  set y := (√(q * s))⁻¹ * x
  have hqs : √(q * s) = √q * √s := Real.sqrt_mul hq.le s
  rw [gaussianD_eq_profile d (by positivity), abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (√(2 * π))⁻¹),
    abs_of_pos (by positivity : (0 : ℝ) < (√(q * s))⁻¹ ^ (d + 1))]
  have hp := hprof y
  have hφ : gaussProfile y = Real.exp (-(q / l) * y ^ 2 / 2) * Real.exp (-ε * y ^ 2) := by
    unfold gaussProfile; rw [← Real.exp_add]; congr 1; simp only [ε]; ring
  have hx : Real.exp (-(x ^ 2) / (2 * (l * s))) = Real.exp (-(q / l) * y ^ 2 / 2) := by
    congr 1
    simp only [y]
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hg : gaussian (l * s) x = (√(2 * π))⁻¹ * (√l)⁻¹ * (√s)⁻¹ *
      Real.exp (-(q / l) * y ^ 2 / 2) := by
    unfold gaussian
    rw [hx, show 2 * π * (l * s) = (2 * π) * l * s by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
    rw [mul_inv, mul_inv]
  have hpow : √s ^ d * (√(q * s))⁻¹ ^ (d + 1) = (√q)⁻¹ ^ (d + 1) * (√s)⁻¹ := by
    rw [hqs, mul_inv, mul_pow, pow_succ (√s)⁻¹, inv_pow (√s) d]
    field_simp
  have hE := Real.exp_pos (-(q / l) * y ^ 2 / 2)
  calc √s ^ d * ((√(2 * π))⁻¹ * (√(q * s))⁻¹ ^ (d + 1) * |gaussProfileD d y|)
      = (√(2 * π))⁻¹ * (√s ^ d * (√(q * s))⁻¹ ^ (d + 1)) * |gaussProfileD d y| := by ring
    _ ≤ (√(2 * π))⁻¹ * (√s ^ d * (√(q * s))⁻¹ ^ (d + 1)) *
          (C0 * (1 + |y|) ^ d * gaussProfile y) := by gcongr
    _ = (√(2 * π))⁻¹ * ((√q)⁻¹ ^ (d + 1) * (√s)⁻¹) * C0 *
          ((1 + |y|) ^ d * Real.exp (-ε * y ^ 2)) * Real.exp (-(q / l) * y ^ 2 / 2) := by
        rw [hpow, hφ]; ring
    _ ≤ (√(2 * π))⁻¹ * ((√q)⁻¹ ^ (d + 1) * (√s)⁻¹) * C0 * B *
          Real.exp (-(q / l) * y ^ 2 / 2) := by gcongr; exact hB y
    _ = (√q)⁻¹ ^ (d + 1) * C0 * B * √l * gaussian (l * s) x := by rw [hg]; field_simp
end GaussianComparison
section TraceExpansion
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def planePt (q : Fin 2 → ℝ) : Fin 3 → ℝ := ![q 0, q 1, -q 0 - q 1]
end TraceExpansion
section VertexDerivatives
def dexp (m : ℕ) (v : Fin 3) : ℕ := if v = 0 ∧ m = 4 then 2 else 1
def Dfun (d : ℕ) (s x : ℝ) : ℝ :=
  √s ^ d * gaussianD d (21 / 20 * s) x / gaussian (11 / 10 * s) x
def acoef (j : ℕ) (s d : ℝ) : ℝ :=
  -(√s ^ j * gaussianD (j - 1) (1 / 20 * s) d / gaussian (1 / 10 * s) d)
lemma gaussian_pos {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : 0 < gaussian σ t := by
  unfold gaussian
  have : 0 < √(2 * π * σ) := Real.sqrt_pos.2 (by positivity)
  positivity
lemma Dfun_bound (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 < s → ∀ x, |Dfun d s x| ≤ C := by
  obtain ⟨C, hC, h⟩ := gaussianD_ratio_le d (q := 21 / 20) (l := 11 / 10) (by norm_num)
    (by norm_num)
  refine ⟨C, hC, fun s hs x => ?_⟩
  have hg := gaussian_pos (by positivity : (0 : ℝ) < 11 / 10 * s) x
  rw [Dfun, abs_div, abs_of_pos hg, abs_mul, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _),
    div_le_iff₀ hg]
  exact h s hs x
lemma acoef_bound (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, 0 < s → ∀ d, |acoef j s d| ≤ C * √s := by
  obtain ⟨C, hC, h⟩ := gaussianD_ratio_le (j - 1) (q := 1 / 20) (l := 1 / 10) (by norm_num)
    (by norm_num)
  refine ⟨C, hC, fun s hs d => ?_⟩
  have hg := gaussian_pos (by positivity : (0 : ℝ) < 1 / 10 * s) d
  rw [acoef, abs_neg, abs_div, abs_of_pos hg, abs_mul,
    abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), div_le_iff₀ hg]
  have hj' : j = (j - 1) + 1 := by omega
  rw [hj', pow_succ]
  have := h s hs d
  have hs' := Real.sqrt_nonneg s
  calc √s ^ (j - 1) * √s * |gaussianD (j - 1 + 1 - 1) (1 / 20 * s) d|
      = √s * (√s ^ (j - 1) * |gaussianD (j - 1) (1 / 20 * s) d|) := by
        rw [show j - 1 + 1 - 1 = j - 1 by omega]; ring
    _ ≤ √s * (C * gaussian (1 / 10 * s) d) := mul_le_mul_of_nonneg_left this hs'
    _ = _ := by ring
end VertexDerivatives
section GaussianAverages
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def avgMeasure (s : ℝ) : Measure ℝ :=
  volume.withDensity fun d => ((gaussian (1 / 10 * s) d).toNNReal : ℝ≥0∞)
instance avgMeasure_prob {s : ℝ} [Fact (0 < s)] : IsProbabilityMeasure (avgMeasure s) := by
  have hs : 0 < s := Fact.out
  constructor
  rw [avgMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have : ∫⁻ d, ((gaussian (1 / 10 * s) d).toNNReal : ℝ≥0∞) =
      ENNReal.ofReal (∫ d, gaussian (1 / 10 * s) d) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_gaussian' (by positivity))
      (Eventually.of_forall fun d => gaussian_nonneg' _ _)]
    rfl
  rw [this, integral_gaussian_eq_one (by positivity), ENNReal.ofReal_one]
end GaussianAverages
section WeightedCostComparison
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end WeightedCostComparison
section PlaneShifts
def shiftMat (v : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ := fun r c =>
  if c = 2 then (if r = v then 1 else 0) else (if r = 2 then -1 else if r = c then 1 else 0)
end PlaneShifts
section AveragedTrace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
def Dmat (m : ℕ) (v : Fin 3) (p : Fin 3 → ℝ) (s : ℝ) : Matrix ι ι ℂ :=
  rdiag fun i => Dfun (dexp m v) s (Hd.u i - p v)
def baseTrace (m : ℕ) (p : Fin 3 → ℝ) (s : ℝ) : ℂ :=
  (Hd.Dmat m 0 p s * Hd.W p (fun _ => 11 / 10 * s) 0 * Hd.Dmat m 1 p s *
    Hd.W p (fun _ => 11 / 10 * s) 1 * Hd.Dmat m 2 p s * Hd.W p (fun _ => 11 / 10 * s) 2).trace
end HeatData
end AveragedTrace
section GaussianIntervalKernel
def Kern (m : ℕ) (a b t : ℝ) : ℝ := ∫ s in a..b, √s ^ m * gaussianD m (63 / 20 * s) t / s
end GaussianIntervalKernel
section CostMeasurability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace HeatData
variable (Hd : HeatData ι)
end HeatData
end CostMeasurability
section VarianceChoices
def rateAt (v : Fin 3) : Fin 3 → ℝ := fun k => if k = v then 1 else 11 / 10
def constD : ℝ := Classical.choose (Dfun_bound 1) + Classical.choose (Dfun_bound 2)
def constA : ℝ := Classical.choose (acoef_bound 1 le_rfl) +
  Classical.choose (acoef_bound 2 (by norm_num))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end VarianceChoices
section NormNormalization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end NormNormalization
end
end Auto
@[expose] public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
namespace Auto
noncomputable section
section Kernels
def kernIntegrand (m : ℕ) (s t : ℝ) : ℝ := √s ^ m * gaussianD m (63 / 20 * s) t / s
end Kernels
end
end Auto
@[expose] public section
namespace Auto
open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
def heatCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Hd : HeatData ι) (α : Fin 3 → ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Gm (1 / 10) 0 z.1 z.2) *
    ∑ v, matCost (Hd.T z.2 (HeatData.sig α z.1) v) (Hd.Ui z.2 (HeatData.sig α z.1) v)
end
end Auto
namespace Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
def gridGaussianForm {ι : Type*} [Fintype ι] (Hd : HeatData ι) (a b : ℝ) : ℂ :=
  (Hd.h ^ 3 : ℂ) * ∑ i, ∑ j, ∑ k,
    Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i *
      (Kern 3 a b (Hd.u i + Hd.u j + Hd.u k) : ℂ)
def heatBoundConstant : ℝ :=
  (5 / 3 * constD * constA ^ 2) * 3 *
    (28 * (2 * Real.sqrt 2 * (1 + Real.sqrt (2 / Real.pi))))
def scaleHeatData {ι : Type*} (Hd : HeatData ι) (c : Fin 3 → ℂ) : HeatData ι :=
  ⟨Hd.u, Hd.h, fun v => c v • Hd.A v⟩
end
end Auto
namespace Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
def sourceGaussianIntegrand (F : Fin 3 → ℝ × ℝ → ℂ) (a b : ℝ)
    (x : Fin 3 → ℝ) : ℂ :=
  F 0 (x 0, x 1) * F 1 (x 1, x 2) * F 2 (x 2, x 0) *
    (Kern 3 a b (x 0 + x 1 + x 2) : ℂ)
def compactCutoff (n : ℕ) (p : ℝ × ℝ) : ℝ := max 0 (min 1 (n + 1 - ‖p‖))
end
end Auto
namespace Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
def triangularGaussianPrimitive (c s t : ℝ) : ℝ :=
  (2 / (c * Real.sqrt (2 * Real.pi * c) * t)) *
    ((1 - t ^ 2 / (c * s)) * Real.exp (-(t ^ 2 / (c * s)) / 2))
def triangularCutoffProfile (u : ℝ) : ℝ := (1 - 2 * u) * Real.exp (-u)
def triangularKernelCoefficient : ℝ :=
  2 / ((63 / 20 : ℝ) * Real.sqrt (2 * Real.pi * (63 / 20)))
def triangularShiftProduct (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) (t : ℝ) : ℂ :=
  F (p.1 + t, p.2) * G (p.1, p.2 + t)
def triangularOddQuotient (H F G : ℝ × ℝ → ℂ) (q : (ℝ × ℝ) × ℝ) : ℂ :=
  H q.1 * (triangularShiftProduct F G q.1 q.2 -
    triangularShiftProduct F G q.1 (-q.2)) / (q.2 : ℂ)
theorem triangularOddQuotient_bound {H F G : ℝ × ℝ → ℂ} {M : ℝ≥0} (hF : LipschitzWith M F)
    (hG : LipschitzWith M G) (bF : ∀ p, ‖F p‖ ≤ M) (bG : ∀ p, ‖G p‖ ≤ M) (p : ℝ × ℝ) (t : ℝ) :
    ‖triangularOddQuotient H F G (p, t)‖ ≤ ‖H p‖ * (4 * (M : ℝ) ^ 2) := by
  by_cases ht : t = 0
  · simp only [triangularOddQuotient, ht, neg_zero, sub_self, mul_zero,
      Complex.ofReal_zero, div_zero, norm_zero]
    positivity
  have hdF : ‖F (p.1 + t, p.2) - F (p.1 - t, p.2)‖ ≤ (M : ℝ) * (2 * |t|) := by
    have h := hF.norm_sub_le (p.1 + t, p.2) (p.1 - t, p.2)
    have he : (p.1 + t, p.2) - (p.1 - t, p.2) = (2 * t, 0) := by ext <;> simp; ring
    simpa [he, Prod.norm_def, Real.norm_eq_abs, abs_mul] using h
  have hdG : ‖G (p.1, p.2 + t) - G (p.1, p.2 - t)‖ ≤ (M : ℝ) * (2 * |t|) := by
    have h := hG.norm_sub_le (p.1, p.2 + t) (p.1, p.2 - t)
    have he : (p.1, p.2 + t) - (p.1, p.2 - t) = (0, 2 * t) := by ext <;> simp; ring
    simpa [he, Prod.norm_def, Real.norm_eq_abs, abs_mul] using h
  have hd : ‖triangularShiftProduct F G p t - triangularShiftProduct F G p (-t)‖ ≤
      4 * (M : ℝ) ^ 2 * |t| := by
    unfold triangularShiftProduct; simp only [← sub_eq_add_neg]
    calc
      _ = ‖(F (p.1 + t, p.2) - F (p.1 - t, p.2)) * G (p.1, p.2 + t) +
          F (p.1 - t, p.2) * (G (p.1, p.2 + t) - G (p.1, p.2 - t))‖ := by congr 1; ring
      _ ≤ ‖F (p.1 + t, p.2) - F (p.1 - t, p.2)‖ * ‖G (p.1, p.2 + t)‖ +
          ‖F (p.1 - t, p.2)‖ * ‖G (p.1, p.2 + t) - G (p.1, p.2 - t)‖ := by
        simpa only [norm_mul] using norm_add_le
          ((F (p.1 + t, p.2) - F (p.1 - t, p.2)) * G (p.1, p.2 + t))
          (F (p.1 - t, p.2) * (G (p.1, p.2 + t) - G (p.1, p.2 - t)))
      _ ≤ ((M : ℝ) * (2 * |t|)) * M + M * (M * (2 * |t|)) := by
        gcongr <;> first | exact hdF | exact hdG | exact bF _ | exact bG _
      _ = _ := by ring
  rw [triangularOddQuotient, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    div_le_iff₀ (abs_pos.mpr ht)]
  nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg (H p))]
theorem triangular_schwartz_bounds (F : SchwartzMap (ℝ × ℝ) ℂ) :
    ∃ M : ℝ≥0, LipschitzWith M F ∧ (∀ p, ‖F p‖ ≤ M) ∧ ∀ p : ℝ × ℝ, ‖F p‖ ≤ (M : ℝ) * (1 + p.1 ^
      2)⁻¹ := by
  let A := SchwartzMap.seminorm ℝ 0 0 F
  let B := SchwartzMap.seminorm ℝ 2 0 F
  let D := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) ℂ F)
  have hA : 0 ≤ A := apply_nonneg _ _
  have hB : 0 ≤ B := apply_nonneg _ _
  have hD : 0 ≤ D := apply_nonneg _ _
  let M : ℝ≥0 := ⟨A + B + D, by positivity⟩
  have hsize : ∀ p, ‖F p‖ ≤ (M : ℝ) := by
    intro p
    have h := F.norm_le_seminorm ℝ p
    change ‖F p‖ ≤ A at h
    change ‖F p‖ ≤ A + B + D
    linarith
  refine ⟨M, ?_, hsize, ?_⟩
  · apply lipschitzWith_of_nnnorm_fderiv_le F.differentiable
    intro p
    have h := (SchwartzMap.fderivCLM ℝ (ℝ × ℝ) ℂ F).norm_le_seminorm ℝ p
    change ‖fderiv ℝ F p‖ ≤ D at h
    change ‖fderiv ℝ F p‖₊ ≤ M
    apply NNReal.coe_le_coe.mp
    change ‖fderiv ℝ F p‖ ≤ A + B + D
    linarith
  · intro p
    have h0 := F.norm_le_seminorm ℝ p
    have h2 := F.norm_pow_mul_le_seminorm ℝ 2 p
    have hp : |p.1| ≤ ‖p‖ := by simp [Prod.norm_def, Real.norm_eq_abs]
    have hp2 : p.1 ^ 2 ≤ ‖p‖ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg p.1) hp 2
    change ‖F p‖ ≤ A at h0
    change ‖p‖ ^ 2 * ‖F p‖ ≤ B at h2
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    change ‖F p‖ * (1 + p.1 ^ 2) ≤ A + B + D
    nlinarith [mul_le_mul_of_nonneg_right hp2 (norm_nonneg (F p))]
theorem triangular_integrable_decay {H : ℝ × ℝ → ℝ} (hH : Integrable H) (sign : ℝ)
    (hsign : sign = 1 ∨ sign = -1) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => H q.1 * (1 + (q.1.1 + sign * q.2) ^ 2)⁻¹) := by
  have hbase := hH.mul_prod integrable_inv_one_add_sq
  have hp : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => (q.1, q.1.1 + sign * q.2))
      (volume.prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure (ℝ × ℝ))).skew_product
      (g := fun (p : ℝ × ℝ) (t : ℝ) => p.1 + sign * t)
      (μc := volume) (μd := volume) (by fun_prop) ?_
    filter_upwards [] with p
    rcases hsign with rfl | rfl
    · simpa using (measurePreserving_add_left volume p.1).map_eq
    · have h := (measurePreserving_add_left volume p.1).comp (Measure.measurePreserving_neg (volume
        : Measure ℝ))
      simpa [Function.comp_def] using h.map_eq
  exact hp.integrable_comp_of_integrable hbase
theorem triangularOddQuotient_tail_bound {H F G : ℝ × ℝ → ℂ} {M : ℝ≥0}
    (bF : ∀ p : ℝ × ℝ, ‖F p‖ ≤ (M : ℝ) * (1 + p.1 ^ 2)⁻¹) (bG : ∀ p, ‖G p‖ ≤ M) (p : ℝ × ℝ)
    (t : ℝ) (ht : 1 ≤ |t|) :
    ‖triangularOddQuotient H F G (p, t)‖ ≤ ‖H p‖ * (M : ℝ) ^ 2 * ((1 + (p.1 + t) ^ 2)⁻¹ + (1 +
      (p.1 - t) ^ 2)⁻¹) := by
  have hd : ‖triangularShiftProduct F G p t - triangularShiftProduct F G p (-t)‖ ≤
      (M : ℝ) ^ 2 * ((1 + (p.1 + t) ^ 2)⁻¹ + (1 + (p.1 - t) ^ 2)⁻¹) := by
    calc
      _ ≤ ‖triangularShiftProduct F G p t‖ + ‖triangularShiftProduct F G p (-t)‖ := norm_sub_le _ _
      _ = ‖F (p.1 + t, p.2)‖ * ‖G (p.1, p.2 + t)‖ +
          ‖F (p.1 - t, p.2)‖ * ‖G (p.1, p.2 - t)‖ := by
        simp [triangularShiftProduct, sub_eq_add_neg]
      _ ≤ ((M : ℝ) * (1 + (p.1 + t) ^ 2)⁻¹) * M +
          (M * (1 + (p.1 - t) ^ 2)⁻¹) * M := by
        gcongr <;> first | exact bF _ | exact bG _
      _ = _ := by ring
  rw [triangularOddQuotient, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖H p‖ * ((M : ℝ) ^ 2 *
        ((1 + (p.1 + t) ^ 2)⁻¹ + (1 + (p.1 - t) ^ 2)⁻¹)) / |t| := by gcongr
    _ ≤ ‖H p‖ * ((M : ℝ) ^ 2 *
        ((1 + (p.1 + t) ^ 2)⁻¹ + (1 + (p.1 - t) ^ 2)⁻¹)) :=
      div_le_self (by positivity) ht
    _ = _ := by ring
theorem triangularOddQuotient_integrable_of_bounds {H F G : ℝ × ℝ → ℂ} {M : ℝ≥0}
    (hH : Continuous H) (iH : Integrable H) (hF : LipschitzWith M F) (hG : LipschitzWith M G)
    (bF : ∀ p, ‖F p‖ ≤ M) (bG : ∀ p, ‖G p‖ ≤ M)
    (dF : ∀ p : ℝ × ℝ, ‖F p‖ ≤ (M : ℝ) * (1 + p.1 ^ 2)⁻¹) :
    Integrable (triangularOddQuotient H F G) := by
  let j : ℝ → ℝ := (Set.Icc (-1 : ℝ) 1).indicator (fun _ => 1)
  have ij : Integrable j :=
    (integrableOn_const (measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
  have i0 := (iH.norm.mul_prod ij).const_mul (4 * (M : ℝ) ^ 2)
  have ip := (triangular_integrable_decay iH.norm 1 (Or.inl rfl)).const_mul ((M : ℝ) ^ 2)
  have im := (triangular_integrable_decay iH.norm (-1) (Or.inr rfl)).const_mul ((M : ℝ) ^ 2)
  apply ((i0.add ip).add im).mono'
  · have hFc := hF.continuous
    have hGc := hG.continuous
    apply Measurable.aestronglyMeasurable
    unfold triangularOddQuotient triangularShiftProduct
    fun_prop
  · filter_upwards [] with q
    dsimp only [Pi.add_apply]
    have hb0 := triangularOddQuotient_bound (H := H) hF hG bF bG q.1 q.2
    have hp0 : 0 ≤ (M : ℝ) ^ 2 * (‖H q.1‖ * (1 + (q.1.1 + q.2) ^ 2)⁻¹) := by positivity
    have hm0 : 0 ≤ (M : ℝ) ^ 2 * (‖H q.1‖ * (1 + (q.1.1 - q.2) ^ 2)⁻¹) := by positivity
    by_cases ht : q.2 ∈ Set.Icc (-1 : ℝ) 1
    · simp only [j, Set.indicator_of_mem ht, mul_one, one_mul, neg_one_mul, ← sub_eq_add_neg]
      nlinarith
    · have habs : 1 ≤ |q.2| := by
        have hnot : ¬ |q.2| ≤ 1 := by simpa only [abs_le, Set.mem_Icc] using ht
        exact le_of_lt (lt_of_not_ge hnot)
      have hb := triangularOddQuotient_tail_bound (H := H) dF bG q.1 q.2 habs
      simp only [j, Set.indicator_of_notMem ht, mul_zero, zero_add, one_mul,
        neg_one_mul, ← sub_eq_add_neg]
      nlinarith
theorem triangularOddQuotient_integrable (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Integrable (triangularOddQuotient H F G) := by
  obtain ⟨MF, hF, bF, dF⟩ := triangular_schwartz_bounds F
  obtain ⟨MG, hG, bG, _⟩ := triangular_schwartz_bounds G
  have hMF : MF ≤ MF + MG := le_add_of_nonneg_right zero_le
  have hMG : MG ≤ MF + MG := le_add_of_nonneg_left zero_le
  apply triangularOddQuotient_integrable_of_bounds H.continuous H.integrable
    (hF.weaken hMF) (hG.weaken hMG)
  · intro p; exact (bF p).trans (NNReal.coe_le_coe.mpr hMF)
  · intro p; exact (bG p).trans (NNReal.coe_le_coe.mpr hMG)
  · intro p
    exact (dF p).trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hMF) (by positivity))
def triangularPV (H F G : SchwartzMap (ℝ × ℝ) ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * ∫ q, triangularOddQuotient H F G q
def triangularTruncation (H F G : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) : ℂ :=
  ∫ q : (ℝ × ℝ) × ℝ, if ε < |q.2| then
    H q.1 * triangularShiftProduct F G q.1 q.2 / (q.2 : ℂ) else 0
def triangularPlaneEquiv : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (p.2, -p.1 - p.2)
  invFun p := (-p.1 - p.2, p.1)
  left_inv p := by ext <;> dsimp; ring
  right_inv p := by ext <;> dsimp; ring
  map_add' p q := by ext <;> simp; ring
  map_smul' c p := by ext <;> simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
def triangularPullback₁ : SchwartzMap (ℝ × ℝ) ℂ →L[ℂ] SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ triangularPlaneEquiv
def triangularPullback₂ : SchwartzMap (ℝ × ℝ) ℂ →L[ℂ] SchwartzMap (ℝ × ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ triangularPlaneEquiv.symm
def triangularSpaceEquiv : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ((ℝ × ℝ) × ℝ) where
  toFun q := (q.1, -q.1.1 - q.1.2 - q.2)
  invFun q := (q.1, -q.1.1 - q.1.2 - q.2)
  left_inv q := by ext <;> dsimp; ring
  right_inv q := by ext <;> dsimp; ring
  map_add' p q := by ext <;> simp; ring
  map_smul' c p := by ext <;> simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
def triangularHilbertTruncation (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) (ε : ℝ) : ℂ :=
  ∫ q : (ℝ × ℝ) × ℝ, if ε < |q.1.1 + q.1.2 + q.2| then
    F₀ q.1 * F₁ (q.1.2, q.2) * F₂ (q.2, q.1.1) / ((q.1.1 + q.1.2 + q.2 : ℝ) : ℂ)
    else 0
def triangularHilbert (F₀ F₁ F₂ : SchwartzMap (ℝ × ℝ) ℂ) : ℂ :=
  -triangularPV F₀ (triangularPullback₁ F₁) (triangularPullback₂ F₂)
def fin3Equiv : (Fin 3 → ℝ) ≃ᵐ (ℝ × ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow).trans
      MeasurableEquiv.prodComm)
def sourceGaussianPairing (F : Fin 3 → SchwartzMap (ℝ × ℝ) ℂ) (a b : ℝ)
    (q : (ℝ × ℝ) × ℝ) : ℂ :=
  F 0 q.1 * F 1 (q.1.2, q.2) * F 2 (q.2, q.1.1) *
    (Kern 3 a b (q.1.1 + q.1.2 + q.2) : ℂ)
def triangularBoundConstant : ℝ := 3 * heatBoundConstant / triangularKernelCoefficient
theorem triangularPV_add_1 (H F G H' : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV (H + H') F G = triangularPV H F G + triangularPV H' F G := by
  have he : triangularOddQuotient ((H + H') : SchwartzMap (ℝ × ℝ) ℂ) F G =
      fun q => triangularOddQuotient H F G q + triangularOddQuotient H' F G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.add_apply]; ring
  simp only [triangularPV, he, integral_add
    (triangularOddQuotient_integrable H F G) (triangularOddQuotient_integrable H' F G)]; ring
theorem triangularPV_smul_1 (c : ℂ) (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV (c • H) F G = c • triangularPV H F G := by
  have he : triangularOddQuotient ((c • H) : SchwartzMap (ℝ × ℝ) ℂ) F G =
      fun q => c * triangularOddQuotient H F G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.smul_apply,
        smul_eq_mul]; ring
  simp only [triangularPV, he, integral_const_mul, smul_eq_mul]; ring
theorem triangularPV_add_2 (H F G F' : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV H (F + F') G = triangularPV H F G + triangularPV H F' G := by
  have he : triangularOddQuotient H ((F + F') : SchwartzMap (ℝ × ℝ) ℂ) G =
      fun q => triangularOddQuotient H F G q + triangularOddQuotient H F' G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.add_apply]; ring
  simp only [triangularPV, he, integral_add
    (triangularOddQuotient_integrable H F G) (triangularOddQuotient_integrable H F' G)]; ring
theorem triangularPV_smul_2 (c : ℂ) (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV H (c • F) G = c • triangularPV H F G := by
  have he : triangularOddQuotient H ((c • F) : SchwartzMap (ℝ × ℝ) ℂ) G =
      fun q => c * triangularOddQuotient H F G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.smul_apply,
        smul_eq_mul]; ring
  simp only [triangularPV, he, integral_const_mul, smul_eq_mul]; ring
theorem triangularPV_add_3 (H F G G' : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV H F (G + G') = triangularPV H F G + triangularPV H F G' := by
  have he : triangularOddQuotient H F ((G + G') : SchwartzMap (ℝ × ℝ) ℂ) =
      fun q => triangularOddQuotient H F G q + triangularOddQuotient H F G' q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.add_apply]; ring
  simp only [triangularPV, he, integral_add
    (triangularOddQuotient_integrable H F G) (triangularOddQuotient_integrable H F G')]; ring
theorem triangularPV_smul_3 (c : ℂ) (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    triangularPV H F (c • G) = c • triangularPV H F G := by
  have he : triangularOddQuotient H F ((c • G) : SchwartzMap (ℝ × ℝ) ℂ) =
      fun q => c * triangularOddQuotient H F G q := by
    funext q; simp only [triangularOddQuotient, triangularShiftProduct, _root_.smul_apply,
        smul_eq_mul]; ring
  simp only [triangularPV, he, integral_const_mul, smul_eq_mul]; ring
def triangularPVLinear :
    SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun H F => {
      toFun := fun G => triangularPV H F G
      map_add' := fun G G' => triangularPV_add_3 H F G G'
      map_smul' := fun c G => triangularPV_smul_3 c H F G })
    (fun H H' F => by ext G; exact triangularPV_add_1 H F G H')
    (fun c H F => by ext G; exact triangularPV_smul_1 c H F G)
    (fun H F F' => by ext G; exact triangularPV_add_2 H F G F')
    (fun c H F => by ext G; exact triangularPV_smul_2 c H F G)
def triangularHilbertLinear :
    SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] SchwartzMap (ℝ × ℝ) ℂ →ₗ[ℂ] ℂ :=
  -((triangularPVLinear.compl₂ triangularPullback₁.toLinearMap).compr₂
    (LinearMap.lcomp ℂ ℂ triangularPullback₂.toLinearMap))
section DenseExtension
variable {𝕜 E V W : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W] [CompleteSpace
    W]
end DenseExtension
instance triangular_fact_one_le_three : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩
abbrev TriangularL3 := Lp ℂ 3 (volume : Measure (ℝ × ℝ))
section Statements
end Statements
end
end Auto


