-- Prove2me | solution 1 for ArtinPrimitiveRoots.major_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T20:27:26.485348+00:00
-- url     : https://prove2.me/submissions/c356d7e2-f3dd-4ebe-89b3-5ea1be89c1d6

import Mathlib
import Definitions.Def_ArtinMarkedSquare
import Theorems.Thm_ArtinPrimitiveRoots_dirichlet_mean_value
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals
import Theorems.Thm_ArtinPrimitiveRoots_arc_cutoff_mellin_separation
import Theorems.Thm_ArtinPrimitiveRoots_small_prime_sparse_mean

section
/-!
# L102M: shared basic definitions and lemmas

`arcCutoff` facts, `ψ_λ = psiL`, `n^{iτ}` helpers, and the Cauchy weight `ω_a`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff

noncomputable section

/-- The complexified cutoff. -/
def arcC (y : ℝ) : ℂ := (arcCutoff y : ℂ)

/-- The phase `e(λ y) = exp(2π i λ y)`. -/
def eL (lam y : ℝ) : ℂ := Complex.exp (2 * π * I * lam * y)

/-- `ψ_λ(y) = ψ(y) e(λ y)`. -/
def psiL (lam y : ℝ) : ℂ := arcC y * eL lam y

lemma natCpow_I_mul (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (I * t) = Complex.exp (I * t * Real.log n) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  have h : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [h]; congr 1; ring

lemma norm_natCpow_I_mul (n : ℕ) (hn : 0 < n) (t : ℝ) : ‖(n : ℂ) ^ (I * t)‖ = 1 := by
  rw [natCpow_I_mul n hn t, show I * (t : ℂ) * ((Real.log n : ℝ) : ℂ) =
    ((t * Real.log n : ℝ) : ℂ) * I by rw [Complex.ofReal_mul]; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_natCpow_I_mul (n : ℕ) (hn : 0 < n) :
    Continuous fun t : ℝ => (n : ℂ) ^ (I * t) := by
  have : (fun t : ℝ => (n : ℂ) ^ (I * t)) = fun t : ℝ => Complex.exp (I * t * Real.log n) := by
    funext t; exact natCpow_I_mul n hn t
  rw [this]; fun_prop

lemma natCpow_I_mul_add (n : ℕ) (hn : 0 < n) (s t : ℝ) :
    (n : ℂ) ^ (I * s) * (n : ℂ) ^ (I * t) = (n : ℂ) ^ (I * (s + t : ℝ)) := by
  rw [natCpow_I_mul n hn, natCpow_I_mul n hn, natCpow_I_mul n hn, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- The Cauchy weight `ω_a(τ) = (1 + (τ/a)²)⁻¹`. -/
def ωa (a τ : ℝ) : ℝ := (1 + (τ / a) ^ 2)⁻¹

lemma ωa_pos (a τ : ℝ) : 0 < ωa a τ := by unfold ωa; positivity

lemma integrable_ωa (a : ℝ) (ha : 0 < a) : Integrable (ωa a) := by
  have h := (integrable_inv_one_add_sq).comp_mul_left' (inv_ne_zero ha.ne')
  have e : (fun τ => (1 + (a⁻¹ * τ) ^ 2)⁻¹) = ωa a := by
    funext τ; unfold ωa; rw [div_eq_inv_mul]
  simpa [e] using h

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the mean value theorems, taken from the cut `dirichlet_mean_value`
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset MeasureTheory

theorem mvt (s : Finset ℕ) (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (c : ℕ → ℂ)
    (T₁ T₂ : ℝ) (hT : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, ‖∑ n ∈ s, c n * (n : ℂ) ^ (I * t)‖ ^ 2 ≤
      (T₂ - T₁ + 4 * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2 :=
  (dirichlet_mean_value s N hs c).1 T₁ T₂ hT

theorem wmvt (s : Finset ℕ) (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) (c : ℕ → ℂ)
    (a : ℝ) (ha : 0 < a) :
    ∫ τ, ωa a τ * ‖∑ n ∈ s, c n * (n : ℂ) ^ (I * τ)‖ ^ 2 ≤
      (Real.pi * a + 2 * Real.pi * N * (1 + Real.log N)) * ∑ n ∈ s, ‖c n‖ ^ 2 :=
  (dirichlet_mean_value s N hs c).2 a ha

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the bilinear separation bound

From the Mellin separation: for a bilinear form `G = ∑_{i,j} u_i conj(v_j) ψ_λ(X (w_i - w'_j))`
with `w_i, w'_j ∈ [1, 16]`,
`‖G‖ ≤ K (ε M_U + M_V / ε) / (4X)` whenever `∫ ω_X |U|² ≤ M_U` and
`∫ ω_X(τ) |V(τ - σ)|² dτ ≤ M_V` for all `σ`, where `U, V` are the Dirichlet polynomials
`∑ u_i w_i^{iτ}`, `∑ v_j w'_j^{iτ}` and `ω_X(τ) = (1 + (τ/2πX)²)⁻¹`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory

noncomputable section

/-- The weight `ω_X(τ) = (1 + (τ/(2πX))²)⁻¹`. -/
def ωX (X τ : ℝ) : ℝ := (1 + (τ / (2 * π * X)) ^ 2)⁻¹

lemma ωX_pos (X τ : ℝ) : 0 < ωX X τ := by unfold ωX; positivity

lemma ωX_le_one (X τ : ℝ) : ωX X τ ≤ 1 := by
  unfold ωX
  apply inv_le_one_of_one_le₀
  have := sq_nonneg (τ / (2 * π * X))
  linarith

/-- A generalized Dirichlet polynomial `∑_{i ∈ S} u_i w_i^{iτ}`. -/
def dpoly {ι : Type*} (S : Finset ι) (u : ι → ℂ) (w : ι → ℝ) (τ : ℝ) : ℂ :=
  ∑ i ∈ S, u i * Complex.exp (I * τ * Real.log (w i))

lemma dpoly_continuous {ι : Type*} (S : Finset ι) (u : ι → ℂ) (w : ι → ℝ) :
    Continuous (dpoly S u w) := by
  unfold dpoly
  fun_prop

lemma norm_exp_I_mul (a b : ℝ) : ‖Complex.exp (I * a * b)‖ = 1 := by
  rw [show I * (a : ℂ) * (b : ℂ) = ((a * b : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_dpoly_le {ι : Type*} (S : Finset ι) (u : ι → ℂ) (w : ι → ℝ) (τ : ℝ) :
    ‖dpoly S u w τ‖ ≤ ∑ i ∈ S, ‖u i‖ := by
  unfold dpoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_exp_I_mul, mul_one]

/-- The product weight `w(q) = (1 + q₁²)⁻¹ (1 + q₂²)⁻¹`. -/
def wq (q : ℝ × ℝ) : ℝ := (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹

lemma wq_pos (q : ℝ × ℝ) : 0 < wq q := by unfold wq; positivity

lemma wq_integrable : Integrable wq := by
  have := integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq
  rw [← Measure.volume_eq_prod] at this
  exact this

lemma integrable_wq_mul {f : ℝ × ℝ → ℝ} (hf : Continuous f) (B : ℝ) (hB : ∀ q, |f q| ≤ B) :
    Integrable (fun q => wq q * f q) :=
  wq_integrable.mul_bdd hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hB q)

lemma integral_one_div_scale (X : ℝ) (hX : 0 < X) (h : ℝ → ℝ) :
    ∫ a, h (2 * π * X * a) = (∫ τ, h τ) / (2 * π * X) := by
  rw [Measure.integral_comp_mul_left h (2 * π * X), smul_eq_mul]
  have : 0 < 2 * π * X := by positivity
  rw [abs_of_pos (inv_pos.mpr this)]
  field_simp

lemma integral_wq_U (X : ℝ) (hX : 0 < X) (U : ℝ → ℂ) :
    ∫ q : ℝ × ℝ, wq q * ‖U (2 * π * X * q.1)‖ ^ 2 = (∫ τ, ωX X τ * ‖U τ‖ ^ 2) / (2 * X) := by
  have hX' : 0 < 2 * π * X := by positivity
  have e1 : (fun q : ℝ × ℝ => wq q * ‖U (2 * π * X * q.1)‖ ^ 2) =
      fun q => ((fun a : ℝ => ωX X (2 * π * X * a) * ‖U (2 * π * X * a)‖ ^ 2) q.1) *
        ((fun b : ℝ => (1 + b ^ 2)⁻¹) q.2) := by
    funext q
    simp only [wq, ωX]
    rw [show 2 * π * X * q.1 / (2 * π * X) = q.1 by field_simp]
    ring
  have h := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun a : ℝ => ωX X (2 * π * X * a) * ‖U (2 * π * X * a)‖ ^ 2) (fun b : ℝ => (1 + b ^ 2)⁻¹)
  rw [e1, Measure.volume_eq_prod, h, integral_univ_inv_one_add_sq,
    integral_one_div_scale X hX (fun τ => ωX X τ * ‖U τ‖ ^ 2)]
  field_simp

lemma integral_wq_V_le (X : ℝ) (hX : 0 < X) (V : ℝ → ℂ) (hV : Continuous V) (B : ℝ)
    (hB : ∀ τ, ‖V τ‖ ≤ B) (MV : ℝ) (hMV : ∀ σ, ∫ τ, ωX X τ * ‖V (τ - σ)‖ ^ 2 ≤ MV) :
    ∫ q : ℝ × ℝ, wq q * ‖V (2 * π * X * q.1 - 2 * π * q.2)‖ ^ 2 ≤ MV / (2 * X) := by
  have hX' : 0 < 2 * π * X := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hMV0 : 0 ≤ MV := by
    refine le_trans ?_ (hMV 0)
    exact integral_nonneg fun τ => mul_nonneg (ωX_pos X τ).le (sq_nonneg _)
  have hint : Integrable (fun q : ℝ × ℝ => wq q * ‖V (2 * π * X * q.1 - 2 * π * q.2)‖ ^ 2) := by
    apply integrable_wq_mul (by fun_prop) (B ^ 2)
    intro q
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  have hinner : ∀ b : ℝ, ∫ a : ℝ, wq (a, b) * ‖V (2 * π * X * (a, b).1 - 2 * π * (a, b).2)‖ ^ 2 ≤
      (1 + b ^ 2)⁻¹ * (MV / (2 * π * X)) := by
    intro b
    have e : (fun a : ℝ => wq (a, b) * ‖V (2 * π * X * (a, b).1 - 2 * π * (a, b).2)‖ ^ 2) =
        fun a => (1 + b ^ 2)⁻¹ * ((fun τ => ωX X τ * ‖V (τ - 2 * π * b)‖ ^ 2) (2 * π * X * a)) := by
      funext a
      simp only [wq, ωX]
      rw [show 2 * π * X * a / (2 * π * X) = a by field_simp]
      ring
    rw [e, integral_const_mul,
      integral_one_div_scale X hX (fun τ => ωX X τ * ‖V (τ - 2 * π * b)‖ ^ 2)]
    gcongr
    exact hMV _
  calc ∫ b : ℝ, ∫ a : ℝ, wq (a, b) * ‖V (2 * π * X * (a, b).1 - 2 * π * (a, b).2)‖ ^ 2
      ≤ ∫ b : ℝ, (1 + b ^ 2)⁻¹ * (MV / (2 * π * X)) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun b => integral_nonneg fun a =>
            mul_nonneg (wq_pos _).le (sq_nonneg _)
        · exact integrable_inv_one_add_sq.mul_const _
        · exact Filter.Eventually.of_forall hinner
    _ = MV / (2 * X) := by
        rw [integral_mul_const, integral_univ_inv_one_add_sq]
        field_simp

/-- **Bilinear separation bound.** -/
theorem bilinear_bound (X lam K : ℝ) (hX : 0 < X) (F : ℝ × ℝ → ℂ) (hFc : Continuous F)
    (hFb : ∀ q : ℝ × ℝ, ‖F q‖ ≤ K / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2)))
    (hrep : ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
        psiL lam (X * (w - w')) = ∫ q : ℝ × ℝ, F q *
          Complex.exp (2 * π * I * (q.1 * X * Real.log w + (q.2 - X * q.1) * Real.log w')))
    {ι κ : Type*} (S : Finset ι) (T : Finset κ) (u : ι → ℂ) (v : κ → ℂ) (w : ι → ℝ)
    (w' : κ → ℝ) (hw : ∀ i ∈ S, 1 ≤ w i ∧ w i ≤ 16) (hw' : ∀ j ∈ T, 1 ≤ w' j ∧ w' j ≤ 16)
    (MU MV ε : ℝ) (hε : 0 < ε)
    (hU : ∫ τ, ωX X τ * ‖dpoly S u w τ‖ ^ 2 ≤ MU)
    (hV : ∀ σ : ℝ, ∫ τ, ωX X τ * ‖dpoly T v w' (τ - σ)‖ ^ 2 ≤ MV) :
    ‖∑ i ∈ S, ∑ j ∈ T, u i * (starRingEnd ℂ) (v j) * psiL lam (X * (w i - w' j))‖ ≤
      K * (ε * MU + MV / ε) / (4 * X) := by
  have hK : 0 ≤ K := by
    have h := (norm_nonneg _).trans (hFb 0)
    have hp : 0 < (1 + (0 : ℝ × ℝ).1 ^ 2) * (1 + (0 : ℝ × ℝ).2 ^ 2) := by positivity
    exact (div_nonneg_iff.mp h).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hp))
  have hFb' : ∀ q, ‖F q‖ ≤ K * wq q := by
    intro q; refine (hFb q).trans (le_of_eq ?_); unfold wq; field_simp
  have hFi : Integrable F :=
    (wq_integrable.const_mul K).mono' hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall hFb')
  set A : ℝ × ℝ → ℂ := fun q => dpoly S u w (2 * π * X * q.1) with hA
  set B : ℝ × ℝ → ℂ := fun q => (starRingEnd ℂ) (dpoly T v w' (2 * π * X * q.1 - 2 * π * q.2))
    with hB
  set E : ι → κ → ℝ × ℝ → ℂ := fun i j q =>
    Complex.exp (2 * π * I * (q.1 * X * Real.log (w i) + (q.2 - X * q.1) * Real.log (w' j)))
    with hE
  have hEc : ∀ i j, Continuous (E i j) := fun i j => by rw [hE]; fun_prop
  have hEb : ∀ i j q, ‖E i j q‖ = 1 := by
    intro i j q
    rw [hE]; simp only
    rw [show 2 * π * I * ((q.1 : ℂ) * X * Real.log (w i) + (q.2 - X * q.1) * Real.log (w' j)) =
      ((2 * π * (q.1 * X * Real.log (w i) + (q.2 - X * q.1) * Real.log (w' j)) : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hFE : ∀ i j, Integrable (fun q => F q * E i j q) := fun i j =>
    hFi.mul_bdd (hEc i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => (hEb i j q).le)
  -- step 1: G = ∫ F (A B)
  have hG : ∑ i ∈ S, ∑ j ∈ T, u i * (starRingEnd ℂ) (v j) * psiL lam (X * (w i - w' j)) =
      ∫ q, F q * (A q * B q) := by
    have h1 : ∀ i ∈ S, ∀ j ∈ T, u i * (starRingEnd ℂ) (v j) * psiL lam (X * (w i - w' j)) =
        ∫ q, u i * (starRingEnd ℂ) (v j) * (F q * E i j q) := by
      intro i hi j hj
      rw [hrep _ _ (hw i hi).1 (hw i hi).2 (hw' j hj).1 (hw' j hj).2, integral_const_mul]
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => h1 i hi j hj]
    have h2 : ∀ i ∈ S, ∑ j ∈ T, ∫ q, u i * (starRingEnd ℂ) (v j) * (F q * E i j q) =
        ∫ q, ∑ j ∈ T, u i * (starRingEnd ℂ) (v j) * (F q * E i j q) := fun i _ =>
      (integral_finsetSum _ fun j _ => (hFE i j).const_mul _).symm
    rw [Finset.sum_congr rfl h2, ← integral_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hFE i j).const_mul _]
    apply congrArg
    funext q
    simp only [hA, hB, dpoly, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    rw [hE]; simp only
    rw [← Complex.exp_conj]
    have hc : (starRingEnd ℂ) (I * ((2 * π * X * q.1 - 2 * π * q.2 : ℝ) : ℂ) *
        ((Real.log (w' j) : ℝ) : ℂ)) =
        -(I * ((2 * π * X * q.1 - 2 * π * q.2 : ℝ) : ℂ) * ((Real.log (w' j) : ℝ) : ℂ)) := by
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]; ring
    rw [hc]
    have he : Complex.exp (2 * π * I * (q.1 * X * Real.log (w i) +
        (q.2 - X * q.1) * Real.log (w' j))) =
        Complex.exp (I * ((2 * π * X * q.1 : ℝ) : ℂ) * ((Real.log (w i) : ℝ) : ℂ)) *
        Complex.exp (-(I * ((2 * π * X * q.1 - 2 * π * q.2 : ℝ) : ℂ) *
          ((Real.log (w' j) : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [he]; ring
  -- bounds on A, B
  have hAc : Continuous A := by
    rw [hA]; exact (dpoly_continuous S u w).comp (by fun_prop)
  have hBc : Continuous B := by
    rw [hB]; exact Complex.continuous_conj.comp ((dpoly_continuous T v w').comp (by fun_prop))
  set CA := ∑ i ∈ S, ‖u i‖
  set CB := ∑ j ∈ T, ‖v j‖
  have hAb : ∀ q, ‖A q‖ ≤ CA := fun q => norm_dpoly_le S u w _
  have hBb : ∀ q, ‖B q‖ ≤ CB := fun q => by
    rw [hB]; simp only [Complex.norm_conj]; exact norm_dpoly_le T v w' _
  have hIA : Integrable (fun q => wq q * ‖A q‖ ^ 2) := by
    apply integrable_wq_mul (by fun_prop) (CA ^ 2)
    intro q; rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hAb q) 2
  have hIB : Integrable (fun q => wq q * ‖B q‖ ^ 2) := by
    apply integrable_wq_mul (by fun_prop) (CB ^ 2)
    intro q; rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hBb q) 2
  have hIAv : ∫ q, wq q * ‖A q‖ ^ 2 ≤ MU / (2 * X) := by
    rw [hA]; simp only
    rw [integral_wq_U X hX (dpoly S u w)]
    gcongr
  have hIBv : ∫ q, wq q * ‖B q‖ ^ 2 ≤ MV / (2 * X) := by
    have e : (fun q => wq q * ‖B q‖ ^ 2) =
        fun q => wq q * ‖dpoly T v w' (2 * π * X * q.1 - 2 * π * q.2)‖ ^ 2 := by
      funext q; rw [hB]; simp only [Complex.norm_conj]
    rw [e]
    exact integral_wq_V_le X hX (dpoly T v w') (dpoly_continuous T v w') CB
      (norm_dpoly_le T v w') MV hV
  -- step 2: the AM–GM bound
  have hpt : ∀ q, ‖F q * (A q * B q)‖ ≤
      K / 2 * (ε * (wq q * ‖A q‖ ^ 2) + ε⁻¹ * (wq q * ‖B q‖ ^ 2)) := by
    intro q
    rw [norm_mul, norm_mul]
    have h1 : ‖A q‖ * ‖B q‖ ≤ (ε * ‖A q‖ ^ 2 + ε⁻¹ * ‖B q‖ ^ 2) / 2 := by
      have hε' : 0 < ε⁻¹ := inv_pos.mpr hε
      have : 0 ≤ (ε * ‖A q‖ - ‖B q‖) ^ 2 := sq_nonneg _
      have e : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
      nlinarith [mul_nonneg hε'.le this]
    calc ‖F q‖ * (‖A q‖ * ‖B q‖) ≤ (K * wq q) * ((ε * ‖A q‖ ^ 2 + ε⁻¹ * ‖B q‖ ^ 2) / 2) :=
          mul_le_mul (hFb' q) h1 (by positivity) (mul_nonneg hK (wq_pos q).le)
      _ = K / 2 * (ε * (wq q * ‖A q‖ ^ 2) + ε⁻¹ * (wq q * ‖B q‖ ^ 2)) := by ring
  have hint2 : Integrable (fun q => K / 2 * (ε * (wq q * ‖A q‖ ^ 2) + ε⁻¹ * (wq q * ‖B q‖ ^ 2))) :=
    ((hIA.const_mul ε).add (hIB.const_mul ε⁻¹)).const_mul _
  rw [hG]
  calc ‖∫ q, F q * (A q * B q)‖ ≤ ∫ q, ‖F q * (A q * B q)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ q, K / 2 * (ε * (wq q * ‖A q‖ ^ 2) + ε⁻¹ * (wq q * ‖B q‖ ^ 2)) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _) hint2
        exact Filter.Eventually.of_forall hpt
    _ = K / 2 * (ε * (∫ q, wq q * ‖A q‖ ^ 2) + ε⁻¹ * (∫ q, wq q * ‖B q‖ ^ 2)) := by
        rw [integral_const_mul, integral_add (hIA.const_mul ε) (hIB.const_mul ε⁻¹),
          integral_const_mul, integral_const_mul]
    _ ≤ K / 2 * (ε * (MU / (2 * X)) + ε⁻¹ * (MV / (2 * X))) := by
        gcongr
    _ = K * (ε * MU + MV / ε) / (4 * X) := by
        field_simp
        ring

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the major-arc integral

`majorSquare = ∫_𝔐 G(θ) dθ` with the arc integrand `G = Gth`, and `vol 𝔐 ≤ 16 L^{3A₀}/Y`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory Finset

noncomputable section

/-- The arc kernel `ψ(t/Y) e(θ(t - b + a))`. -/
def kerArc (Y : ℝ) (t a b : ℤ) (θ : ℝ) : ℂ :=
  (arcCutoff (t / Y) : ℂ) * Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))

lemma kerArc_continuous (Y : ℝ) (t a b : ℤ) : Continuous (kerArc Y t a b) := by
  unfold kerArc; fun_prop

/-- The arc integrand `G(θ)`. -/
def Gth (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (θ : ℝ) : ℂ :=
  (squareNorm x a : ℂ) *
    ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
      ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
      ∑ r ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ Finset.range (⌊2 * Hn⌋₊ + 1),
        ((dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) : ℂ) *
          α m * (starRingEnd ℂ) (α r) * β n * (starRingEnd ℂ) (β s) *
          kerArc Y
            (((∏ i, p' i : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) - ((∏ i, p i : ℕ) : ℤ) * (r : ℤ) * (s : ℤ))
            ((∏ i, p i : ℕ) : ℤ) ((∏ i, p' i : ℕ) : ℤ) θ

lemma majorArcs_subset (x A₀ Y : ℝ) : majorArcs x A₀ Y ⊆ Set.Icc 0 1 :=
  fun θ hθ => ⟨hθ.1, hθ.2.1.le⟩

lemma integrableOn_kerArc (x A₀ Y : ℝ) (t a b : ℤ) :
    IntegrableOn (kerArc Y t a b) (majorArcs x A₀ Y) :=
  ((kerArc_continuous Y t a b).integrableOn_Icc).mono_set (majorArcs_subset x A₀ Y)

lemma majorKernel_eq (x A₀ Y : ℝ) (t a b : ℤ) :
    majorKernel x A₀ Y t a b = ∫ θ in majorArcs x A₀ Y, kerArc Y t a b θ := by
  unfold majorKernel kerArc
  rw [integral_const_mul]

/-- `majorSquare = ∫_𝔐 G`. -/
lemma majorSquare_eq_integral (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ)
    (α β : ℕ → ℂ) :
    majorSquare x a A₀ Y Hm Hn α β = ∫ θ in majorArcs x A₀ Y, Gth x a Y Hm Hn α β θ := by
  unfold majorSquare Gth
  simp_rw [majorKernel_eq]
  rw [integral_const_mul]
  congr 1
  have hI : ∀ (c : ℂ) (t a b : ℤ), IntegrableOn (fun θ => c * kerArc Y t a b θ)
      (majorArcs x A₀ Y) := fun c t a b => (integrableOn_kerArc x A₀ Y t a b).const_mul c
  simp_rw [← integral_const_mul]
  rw [integral_finsetSum]
  swap
  · intro p _
    refine integrable_finsetSum _ fun p' _ => integrable_finsetSum _ fun m _ =>
      integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun r _ =>
      integrable_finsetSum _ fun s _ => hI _ _ _ _
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ (fun p' _ => integrable_finsetSum _ fun m _ =>
      integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun r _ =>
      integrable_finsetSum _ fun s _ => hI _ _ _ _)]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ fun n _ =>
      integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun s _ => hI _ _ _ _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ fun r _ =>
      integrable_finsetSum _ fun s _ => hI _ _ _ _)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ fun s _ => hI _ _ _ _)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_finsetSum _ (fun s _ => hI _ _ _ _)]

/-- The measure of the major arcs. -/
lemma volume_majorArcs_le (x A₀ Y : ℝ) (hY : 0 < Y) (hL0 : 0 < Real.log x)
    (hL : 1 ≤ Real.log x ^ A₀) :
    volume.real (majorArcs x A₀ Y) ≤ 16 * Real.log x ^ (3 * A₀) / Y := by
  set Q := ⌊Real.log x ^ A₀⌋₊ with hQ
  set r := 2 * Real.log x ^ A₀ / Y with hr'
  have hr0 : 0 ≤ r := by positivity
  have h3 : Real.log x ^ (3 * A₀) = Real.log x ^ A₀ * Real.log x ^ A₀ * Real.log x ^ A₀ := by
    rw [show 3 * A₀ = A₀ + A₀ + A₀ by ring, Real.rpow_add hL0, Real.rpow_add hL0]
  have hfinI : volume (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by simp
  by_cases hr : r ≤ 1
  swap
  · push_neg at hr
    calc volume.real (majorArcs x A₀ Y) ≤ volume.real (Set.Icc (0 : ℝ) 1) :=
          measureReal_mono (majorArcs_subset x A₀ Y) hfinI
      _ = 1 := by simp
      _ ≤ r := hr.le
      _ ≤ 16 * Real.log x ^ (3 * A₀) / Y := by
          rw [hr', h3]
          apply div_le_div_of_nonneg_right _ hY.le
          nlinarith
  have hsub : majorArcs x A₀ Y ⊆ ⋃ k ∈ Finset.Icc 1 Q,
      ⋃ c ∈ Finset.Icc (-(k : ℤ)) (2 * k), Set.Icc ((c : ℝ) / k - r) ((c : ℝ) / k + r) := by
    intro θ hθ
    obtain ⟨h0, h1, k, hk1, hkL, c, _, hc⟩ := hθ
    have hkQ : k ≤ Q := Nat.le_floor hkL
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    simp only [Set.mem_iUnion, Set.mem_Icc]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkQ⟩, c, ?_, ?_⟩
    · rw [abs_le] at hc
      have h2 : -1 ≤ (c : ℝ) / k := by linarith [hc.1, hc.2]
      have h3 : (c : ℝ) / k ≤ 2 := by linarith [hc.1, hc.2]
      rw [le_div_iff₀ hkpos] at h2
      rw [div_le_iff₀ hkpos] at h3
      rw [Finset.mem_Icc]
      constructor
      · have : ((-(k : ℤ) : ℤ) : ℝ) ≤ c := by push_cast; linarith
        exact_mod_cast this
      · have : (c : ℝ) ≤ ((2 * k : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
    · rw [abs_le] at hc
      constructor <;> linarith [hc.1, hc.2]
  have hcount : ∀ k : ℕ, ((Finset.Icc (-(k : ℤ)) (2 * k)).card : ℝ) ≤ 3 * k + 1 := by
    intro k
    rw [Int.card_Icc]
    have : (2 * (k : ℤ) + 1 - -(k : ℤ)).toNat = 3 * k + 1 := by omega
    rw [this]; push_cast; linarith
  have hQ' : (Q : ℝ) ≤ Real.log x ^ A₀ := Nat.floor_le (by linarith)
  have hsubI : (⋃ k ∈ Finset.Icc 1 Q, ⋃ c ∈ Finset.Icc (-(k : ℤ)) (2 * k),
      Set.Icc ((c : ℝ) / k - r) ((c : ℝ) / k + r)) ⊆ Set.Icc (-3) 4 := by
    intro θ hθ
    simp only [Set.mem_iUnion, Set.mem_Icc, Finset.mem_Icc] at hθ
    obtain ⟨k, ⟨hk1, _⟩, c, ⟨hc1, hc2⟩, h1, h2⟩ := hθ
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have e1 : -1 ≤ (c : ℝ) / k := by
      rw [le_div_iff₀ hkpos]; have : (-(k : ℤ) : ℝ) ≤ c := by exact_mod_cast hc1
      push_cast at this; linarith
    have e2 : (c : ℝ) / k ≤ 2 := by
      rw [div_le_iff₀ hkpos]; have : (c : ℝ) ≤ ((2 * k : ℤ) : ℝ) := by exact_mod_cast hc2
      push_cast at this; linarith
    constructor <;> linarith
  have hfin2 : volume (Set.Icc (-3 : ℝ) 4) ≠ ⊤ := by simp
  calc volume.real (majorArcs x A₀ Y)
      ≤ volume.real (⋃ k ∈ Finset.Icc 1 Q, ⋃ c ∈ Finset.Icc (-(k : ℤ)) (2 * k),
          Set.Icc ((c : ℝ) / k - r) ((c : ℝ) / k + r)) :=
        measureReal_mono hsub (measure_ne_top_of_subset hsubI hfin2)
    _ ≤ ∑ k ∈ Finset.Icc 1 Q, ∑ c ∈ Finset.Icc (-(k : ℤ)) (2 * k),
          volume.real (Set.Icc ((c : ℝ) / k - r) ((c : ℝ) / k + r)) := by
        refine (measureReal_biUnion_finset_le _ _).trans ?_
        exact Finset.sum_le_sum fun k _ => measureReal_biUnion_finset_le _ _
    _ = ∑ k ∈ Finset.Icc 1 Q, ((Finset.Icc (-(k : ℤ)) (2 * k)).card : ℝ) * (2 * r) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have e : ∀ c ∈ Finset.Icc (-(k : ℤ)) (2 * k),
            volume.real (Set.Icc ((c : ℝ) / k - r) ((c : ℝ) / k + r)) = 2 * r := by
          intro c _
          rw [Real.volume_real_Icc_of_le (by linarith)]; ring
        rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.Icc 1 Q, (4 * Real.log x ^ A₀) * (2 * r) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : (k : ℝ) ≤ Real.log x ^ A₀ :=
          le_trans (by exact_mod_cast (Finset.mem_Icc.mp hk).2) hQ'
        gcongr
        linarith [hcount k]
    _ = Q * ((4 * Real.log x ^ A₀) * (2 * r)) := by simp
    _ ≤ Real.log x ^ A₀ * ((4 * Real.log x ^ A₀) * (2 * r)) := by gcongr
    _ = 16 * Real.log x ^ (3 * A₀) / Y := by
        rw [hr', h3]
        field_simp
        ring

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the endpoint polynomials and the weight `f_λ(y) = η(y) e(-λy)`
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset
open scoped ContDiff

noncomputable section

lemma dyadicBump_eq_fun : dyadicBump = fun t => Real.smoothTransition (t - 1) -
    Real.smoothTransition (t / 2 - 1) := rfl

lemma dyadicBump_contDiff : ContDiff ℝ ∞ dyadicBump := by
  rw [dyadicBump_eq_fun]
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.div_const 2).sub contDiff_const))

lemma dyadicBump_eq_zero_of_le_one {t : ℝ} (h : t ≤ 1) : dyadicBump t = 0 := by
  unfold dyadicBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

lemma dyadicBump_eq_zero_of_ge_four {t : ℝ} (h : 4 ≤ t) : dyadicBump t = 0 := by
  unfold dyadicBump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), sub_self]

lemma dyadicBump_nonneg (t : ℝ) : 0 ≤ dyadicBump t := by
  unfold dyadicBump
  rcases le_or_gt t 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]
  · have := Real.smoothTransition.monotone (show t / 2 - 1 ≤ t - 1 by linarith)
    linarith

lemma dyadicBump_le_one (t : ℝ) : dyadicBump t ≤ 1 := by
  unfold dyadicBump
  have h1 := Real.smoothTransition.le_one (t - 1)
  have h2 := Real.smoothTransition.nonneg (t / 2 - 1)
  linarith

lemma dyadicBump_ne_zero {t : ℝ} (h : dyadicBump t ≠ 0) : 1 < t ∧ t < 4 := by
  constructor
  · by_contra h'; exact h (dyadicBump_eq_zero_of_le_one (not_lt.mp h'))
  · by_contra h'; exact h (dyadicBump_eq_zero_of_ge_four (not_lt.mp h'))

lemma dyadicBump_hasCompactSupport : HasCompactSupport dyadicBump := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc 1 4) isCompact_Icc
  intro y hy
  have := dyadicBump_ne_zero hy
  exact ⟨this.1.le, this.2.le⟩

lemma dyadicBump_lipschitz : ∃ Lη : ℝ, 0 ≤ Lη ∧ ∀ y y' : ℝ,
    |dyadicBump y - dyadicBump y'| ≤ Lη * |y - y'| := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport dyadicBump_hasCompactSupport
    dyadicBump_contDiff (by simp)
  refine ⟨C, C.2, fun y y' => ?_⟩
  have := hC.dist_le_mul y y'
  rwa [Real.dist_eq, Real.dist_eq] at this

/-- The weight `f_λ(y) = η(y) e(-λ y)`. -/
def fL (lam y : ℝ) : ℂ := (dyadicBump y : ℂ) * eL (-lam) y

lemma norm_eL (lam y : ℝ) : ‖eL lam y‖ = 1 := by
  unfold eL
  rw [show 2 * (π : ℂ) * I * lam * y = ((2 * π * lam * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma norm_fL_le (lam y : ℝ) : ‖fL lam y‖ ≤ 1 := by
  unfold fL
  rw [norm_mul, norm_eL, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (dyadicBump_nonneg y)]
  exact dyadicBump_le_one y

lemma fL_ne_zero {lam y : ℝ} (h : fL lam y ≠ 0) : 1 < y ∧ y < 4 := by
  apply dyadicBump_ne_zero
  intro h0; apply h; unfold fL; rw [h0]; simp

lemma norm_eL_sub_le (lam y y' : ℝ) : ‖eL lam y - eL lam y'‖ ≤ 2 * π * |lam| * |y - y'| := by
  unfold eL
  rw [show 2 * (π : ℂ) * I * lam * y = I * ((2 * π * lam * y : ℝ) : ℂ) by push_cast; ring,
    show 2 * (π : ℂ) * I * lam * y' = I * ((2 * π * lam * y' : ℝ) : ℂ) by push_cast; ring]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * lam * y - 2 * π * lam * y')
  have e : Complex.exp (I * ((2 * π * lam * y : ℝ) : ℂ)) - Complex.exp (I * ((2 * π * lam * y' : ℝ) : ℂ)) =
      Complex.exp (I * ((2 * π * lam * y' : ℝ) : ℂ)) *
        (Complex.exp (I * ((2 * π * lam * y - 2 * π * lam * y' : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]; congr 2; push_cast; ring
  rw [e, norm_mul, show I * ((2 * π * lam * y' : ℝ) : ℂ) = ((2 * π * lam * y' : ℝ) : ℂ) * I by ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  refine h.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, show 2 * π * lam * y - 2 * π * lam * y' = (2 * π * lam) * (y - y') by ring,
    abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma norm_fL_sub_le (Lη : ℝ) (hLη : ∀ y y' : ℝ, |dyadicBump y - dyadicBump y'| ≤ Lη * |y - y'|)
    (lam y y' : ℝ) : ‖fL lam y - fL lam y'‖ ≤ (Lη + 2 * π * |lam|) * |y - y'| := by
  unfold fL
  have e : (dyadicBump y : ℂ) * eL (-lam) y - (dyadicBump y' : ℂ) * eL (-lam) y' =
      ((dyadicBump y - dyadicBump y' : ℝ) : ℂ) * eL (-lam) y +
        (dyadicBump y' : ℂ) * (eL (-lam) y - eL (-lam) y') := by push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_eL, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (dyadicBump_nonneg y')]
  have h1 := hLη y y'
  have h2 := norm_eL_sub_le (-lam) y y'
  rw [abs_neg] at h2
  have h3 := dyadicBump_le_one y'
  have h4 := dyadicBump_nonneg y'
  have h5 : 0 ≤ ‖eL (-lam) y - eL (-lam) y'‖ := norm_nonneg _
  nlinarith

/-- The label-product polynomial `𝔅_ρ(τ) = ∑_{p, ∏p ≡ ρ} f_λ(∏p / Y) (∏p)^{iτ}`. -/
def Bpoly (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y lam : ℝ) (k : ℕ) (ρ : ZMod k) (τ : ℝ) : ℂ :=
  ∑ p ∈ labelTuples x a, if ((∏ i, p i : ℕ) : ZMod k) = ρ then
    fL lam ((∏ i, p i : ℕ) / Y) * ((∏ i, p i : ℕ) : ℂ) ^ (I * τ) else 0

/-- The residue-class Dirichlet polynomial `∑_{m ≤ 2H, m ≡ ρ} c_m m^{iτ}`. -/
def Rpoly (H : ℝ) (c : ℕ → ℂ) (k : ℕ) (ρ : ZMod k) (τ : ℝ) : ℂ :=
  ∑ m ∈ Finset.range (⌊2 * H⌋₊ + 1), if (m : ZMod k) = ρ then c m * (m : ℂ) ^ (I * τ) else 0

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the arc integrand as a bilinear form

For `θ = c/k + λ/Y`:
`G(θ) = ∏V⁻² ∑_{i, j} u_i conj(u_j) ψ_λ(X (w_i - w_j))`, where `i = (p', m, n)` runs over label
tuples and `m, n`, `u_i = f_λ(b/Y) α_m β_n e(c(bmn - b)/k)` (`b = ∏ p'`), `w_i = bmn/(XY)`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset

noncomputable section

/-- `e(u) = exp(2πiu)`. -/
def ee (u : ℝ) : ℂ := Complex.exp (2 * π * I * u)

lemma norm_ee (u : ℝ) : ‖ee u‖ = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * I * u = ((2 * π * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma conj_ee (u : ℝ) : (starRingEnd ℂ) (ee u) = ee (-u) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal,
    map_ofNat]
  push_cast; ring

lemma ee_int (m : ℤ) : ee m = 1 := by
  unfold ee
  rw [show 2 * (π : ℂ) * I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-- The one-sided index set. -/
def Ix (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Hm Hn : ℝ) : Finset ((Fin K → ℕ) × ℕ × ℕ) :=
  labelTuples x a ×ˢ (Finset.range (⌊2 * Hm⌋₊ + 1) ×ˢ Finset.range (⌊2 * Hn⌋₊ + 1))

/-- The label product `b = ∏ p'`. -/
def bP {K : ℕ} (i : (Fin K → ℕ) × ℕ × ℕ) : ℕ := ∏ j, i.1 j

/-- The one-sided coefficient `u_i`. -/
def uco {K : ℕ} (Y : ℝ) (α β : ℕ → ℂ) (c : ℤ) (k : ℕ) (lam : ℝ)
    (i : (Fin K → ℕ) × ℕ × ℕ) : ℂ :=
  fL lam (bP i / Y) * α i.2.1 * β i.2.2 *
    ee (c * (((bP i * i.2.1 * i.2.2 : ℕ) : ℝ) - (bP i : ℝ)) / k)

/-- The one-sided weight `w_i = bmn/(XY)`. -/
def wco {K : ℕ} (X Y : ℝ) (i : (Fin K → ℕ) × ℕ × ℕ) : ℝ :=
  ((bP i * i.2.1 * i.2.2 : ℕ) : ℝ) / (X * Y)

lemma term_eq (Y X lam : ℝ) (hY : Y ≠ 0) (hX : X ≠ 0) (c : ℤ) (k : ℕ) (hk : k ≠ 0)
    (α β : ℕ → ℂ) {K : ℕ} (p p' : Fin K → ℕ) (m n r s : ℕ) :
    ((dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) : ℝ) : ℂ) *
        α m * (starRingEnd ℂ) (α r) * β n * (starRingEnd ℂ) (β s) *
        kerArc Y (((∏ i, p' i : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) - ((∏ i, p i : ℕ) : ℤ) * (r : ℤ) * (s : ℤ))
          ((∏ i, p i : ℕ) : ℤ) ((∏ i, p' i : ℕ) : ℤ) ((c : ℝ) / k + lam / Y) =
      uco Y α β c k lam (p', m, n) * (starRingEnd ℂ) (uco Y α β c k lam (p, r, s)) *
        psiL lam (X * (wco X Y (p', m, n) - wco X Y (p, r, s))) := by
  unfold uco wco kerArc psiL fL arcC bP
  simp only [map_mul, Complex.conj_ofReal, conj_ee]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have harg : X * (((∏ i, p' i) * m * n : ℕ) / (X * Y) - (((∏ i, p i) * r * s : ℕ) : ℝ) / (X * Y)) =
      (((((∏ i, p' i : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) - ((∏ i, p i : ℕ) : ℤ) * (r : ℤ) * (s : ℤ) : ℤ) : ℝ)
        / Y) := by
    push_cast; field_simp
  rw [harg]
  have heL : ∀ (l y : ℝ), eL l y = ee (l * y) := by
    intro l y; unfold eL ee; push_cast; ring_nf
  rw [heL, heL, heL]
  have hconj : (starRingEnd ℂ) (ee (-lam * ((∏ i, p i : ℕ) / Y))) = ee (lam * ((∏ i, p i : ℕ) / Y)) := by
    rw [conj_ee]; ring_nf
  rw [hconj]
  have hexp : Complex.exp (2 * π * I * ((((c : ℝ) / k + lam / Y) *
      ((((∏ i, p' i : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) - ((∏ i, p i : ℕ) : ℤ) * (r : ℤ) * (s : ℤ) : ℤ) -
        ((∏ i, p' i : ℕ) : ℤ) + ((∏ i, p i : ℕ) : ℤ) : ℝ) : ℝ) : ℂ)) =
      ee (-lam * ((∏ i, p' i : ℕ) / Y)) *
      ee (c * ((((∏ i, p' i) * m * n : ℕ) : ℝ) - ((∏ i, p' i : ℕ) : ℝ)) / k) *
      ee (lam * ((∏ i, p i : ℕ) / Y)) *
      ee (-(c * ((((∏ i, p i) * r * s : ℕ) : ℝ) - ((∏ i, p i : ℕ) : ℝ)) / k)) *
      ee (lam * (((((∏ i, p' i : ℕ) : ℤ) * (m : ℤ) * (n : ℤ) -
        ((∏ i, p i : ℕ) : ℤ) * (r : ℤ) * (s : ℤ) : ℤ) : ℝ) / Y)) := by
    unfold ee
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [hexp]
  push_cast
  ring

/-- **The arc integrand as a bilinear form.** -/
lemma Gth_eq_form (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (lam : ℝ)
    (c : ℤ) (k : ℕ) (hY : Y ≠ 0) (hX : Hm * Hn ≠ 0) (hk : k ≠ 0) :
    Gth x a Y Hm Hn α β ((c : ℝ) / k + lam / Y) = (squareNorm x a : ℂ) *
      ∑ i ∈ Ix x a Hm Hn, ∑ j ∈ Ix x a Hm Hn,
        uco Y α β c k lam i * (starRingEnd ℂ) (uco Y α β c k lam j) *
          psiL lam ((Hm * Hn) * (wco (Hm * Hn) Y i - wco (Hm * Hn) Y j)) := by
  unfold Gth Ix
  congr 1
  simp only [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun s _ => ?_
  exact term_eq Y (Hm * Hn) lam hY hX c k hk α β p p' m n r s

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the prime polynomial `P_𝒮` and the integer window `[H, 2H]`
-/

namespace ArtinPrimitiveRoots.L102M

open Complex Finset

noncomputable section

/-- The normalized prime polynomial `P_𝒮(τ) = P⁻¹ ∑_{p ∈ 𝒮} p^{iτ}`. -/
def Pf (𝒮 : Finset ℕ) (P τ : ℝ) : ℂ := ((P : ℂ))⁻¹ * ∑ p ∈ 𝒮, (p : ℂ) ^ (I * τ)

/-- The integers in `[Hn, 2Hn]`. -/
def Fset (Hn : ℝ) : Finset ℕ := (Finset.range (⌊2 * Hn⌋₊ + 1)).filter (fun n => Hn ≤ n)

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: splitting off a short-interval prime from the label polynomial `𝔅`

With `K = K' + 1` groups, write a label tuple as `(p₀, q)` with `p₀ ∈ 𝒫₀`. Freeze
`f_λ(p₀ ∏q / Y)` on short multiplicative intervals `p₀ ∈ [P_j, P_j e^{δ})` and split `p₀` by its
residue `u` mod `k`:
`𝔅_ρ = ∑_{j,u} P_j P_{𝒮_{j,u}} R_{j,u} + (error ≤ 128 δ Lip Y ∏V)`, `|R_{j,u}| ≤ (4Y/P_j) ∏_{i≥1} V_i`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

lemma sum_piFinset_cons {K' : ℕ} (S : Fin (K' + 1) → Finset ℕ) {M : Type*} [AddCommMonoid M]
    (F : (Fin (K' + 1) → ℕ) → M) :
    ∑ p ∈ Fintype.piFinset S, F p =
      ∑ pq ∈ S 0 ×ˢ Fintype.piFinset (Fin.tail S), F (Fin.cons pq.1 pq.2) := by
  have h := Finset.filter_piFinset_eq_map_consEquiv S (fun _ => True)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
  rw [h, Finset.sum_map]
  rfl

lemma prod_cons_eq {K' : ℕ} (p₀ : ℕ) (q : Fin K' → ℕ) :
    ∏ i, (Fin.cons p₀ q : Fin (K' + 1) → ℕ) i = p₀ * ∏ i, q i := by
  rw [Fin.prod_univ_succ]; simp

/-- Tuples with small product: `#{q : ∏ q ≤ Z} ≤ Z ∏_i ∑_{p ∈ S_i} 1/p`. -/
lemma card_prod_le {K : ℕ} (S : Fin K → Finset ℕ) (hS : ∀ i, ∀ p ∈ S i, 0 < p) (Z : ℝ)
    (hZ : 0 ≤ Z) :
    ∑ q ∈ Fintype.piFinset S, (if ((∏ i, q i : ℕ) : ℝ) ≤ Z then (1 : ℝ) else 0) ≤
      Z * ∏ i, ∑ p ∈ S i, (1 / (p : ℝ)) := by
  have hpt : ∀ q ∈ Fintype.piFinset S, (if ((∏ i, q i : ℕ) : ℝ) ≤ Z then (1 : ℝ) else 0) ≤
      Z * ∏ i, (1 / (q i : ℝ)) := by
    intro q hq
    rw [Fintype.mem_piFinset] at hq
    have hpos : 0 < ((∏ i, q i : ℕ) : ℝ) := by
      have := Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hS i (q i) (hq i)
      exact_mod_cast this
    have e : Z * ∏ i, (1 / (q i : ℝ)) = Z / ((∏ i, q i : ℕ) : ℝ) := by
      push_cast; rw [Finset.prod_div_distrib, prod_const_one]; ring
    rw [e]
    split_ifs with h
    · rw [le_div_iff₀ hpos, one_mul]; exact h
    · positivity
  calc ∑ q ∈ Fintype.piFinset S, (if ((∏ i, q i : ℕ) : ℝ) ≤ Z then (1 : ℝ) else 0)
      ≤ ∑ q ∈ Fintype.piFinset S, Z * ∏ i, (1 / (q i : ℝ)) := sum_le_sum hpt
    _ = Z * ∏ i, ∑ p ∈ S i, (1 / (p : ℝ)) := by
        rw [← mul_sum, Finset.prod_univ_sum]

lemma exp_sub_one_le_two_mul (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : Real.exp δ - 1 ≤ 2 * δ := by
  have := Real.abs_exp_sub_one_le (x := δ) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  exact (le_abs_self _).trans this

variable (x : ℝ) {K' : ℕ} (a : Fin (K' + 1) → ℝ) (Y lam δs : ℝ) (k : ℕ) [NeZero k] (ρ : ZMod k)

/-- The lower end `P₋ = exp(L^{a₀})` of the first prime group. -/
def Plo : ℝ := Real.exp (Real.log x ^ a 0)

/-- The short-interval index of `p₀`. -/
def jf (p : ℕ) : ℕ := ⌊Real.log (p / Plo x a) / δs⌋₊

/-- The representative `P_j = P₋ e^{jδ}`. -/
def Pj (j : ℕ) : ℝ := Plo x a * Real.exp (j * δs)

/-- The number of short intervals. -/
def Jn : ℕ := ⌊Real.log x ^ a 0 / δs⌋₊ + 1

/-- The prime piece `𝒮_{j,u}`. -/
def Spiece (j : ℕ) (u : ZMod k) : Finset ℕ :=
  (primeGroup x (a 0)).filter (fun p => jf x a δs p = j ∧ (p : ZMod k) = u)

/-- The rest polynomial `R_{j,u}`. -/
def Rrest (j : ℕ) (u : ZMod k) (τ : ℝ) : ℂ :=
  ∑ q ∈ Fintype.piFinset (fun i : Fin K' => primeGroup x (a i.succ)),
    if u * ((∏ i, q i : ℕ) : ZMod k) = ρ then
      fL lam (Pj x a δs j * (∏ i, q i : ℕ) / Y) * ((∏ i, q i : ℕ) : ℂ) ^ (I * τ) else 0

/-- The main part of the decomposition. -/
def Bmain (τ : ℝ) : ℂ :=
  ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
    (Pj x a δs j : ℂ) * Pf (Spiece x a δs k j u) (Pj x a δs j) τ * Rrest x a Y lam δs k ρ j u τ

lemma mem_primeGroup_bounds {x y : ℝ} {p : ℕ} (hp : p ∈ primeGroup x y) :
    p.Prime ∧ Real.exp (Real.log x ^ y) ≤ p ∧ (p : ℝ) ≤ Real.exp (2 * Real.log x ^ y) := by
  unfold primeGroup at hp
  rw [mem_filter, mem_range] at hp
  refine ⟨hp.2.1, hp.2.2, ?_⟩
  have : p ≤ ⌊Real.exp (2 * Real.log x ^ y)⌋₊ := by omega
  exact (Nat.le_floor_iff (Real.exp_pos _).le).mp this

lemma jf_bounds (hδ0 : 0 < δs) {p : ℕ} (hp : p ∈ primeGroup x (a 0)) :
    jf x a δs p < Jn x a δs ∧ Pj x a δs (jf x a δs p) ≤ p ∧
      (p : ℝ) < Pj x a δs (jf x a δs p) * Real.exp δs := by
  obtain ⟨_, h1, h2⟩ := mem_primeGroup_bounds hp
  have hP0 : 0 < Plo x a := Real.exp_pos _
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le hP0 h1
  set t := Real.log (p / Plo x a) with ht
  have ht0 : 0 ≤ t := Real.log_nonneg (by rw [le_div_iff₀ hP0, one_mul]; exact h1)
  have htL : t ≤ Real.log x ^ a 0 := by
    rw [ht, Real.log_div hp0.ne' hP0.ne', Plo, Real.log_exp]
    have := Real.log_le_log hp0 h2
    rw [Real.log_exp] at this
    linarith
  have hq : 0 ≤ t / δs := div_nonneg ht0 hδ0.le
  refine ⟨?_, ?_, ?_⟩
  · unfold jf Jn
    rw [← ht, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right htL hδ0.le)
  · unfold Pj
    have hfl : (jf x a δs p : ℝ) * δs ≤ t := by
      have := Nat.floor_le hq
      unfold jf; rw [← ht]
      rwa [le_div_iff₀ hδ0] at this
    calc Plo x a * Real.exp (jf x a δs p * δs) ≤ Plo x a * Real.exp t := by gcongr
      _ = p := by rw [ht, Real.exp_log (div_pos hp0 hP0)]; field_simp
  · unfold Pj
    have hfl : t < ((jf x a δs p : ℝ) + 1) * δs := by
      have := Nat.lt_floor_add_one (t / δs)
      unfold jf; rw [← ht]
      rwa [div_lt_iff₀ hδ0] at this
    calc (p : ℝ) = Plo x a * Real.exp t := by
          rw [ht, Real.exp_log (div_pos hp0 hP0)]; field_simp
      _ < Plo x a * Real.exp (((jf x a δs p : ℝ) + 1) * δs) := by gcongr
      _ = Plo x a * Real.exp (jf x a δs p * δs) * Real.exp δs := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf

lemma natCpow_I_mul_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (τ : ℝ) :
    ((m * n : ℕ) : ℂ) ^ (I * τ) = (m : ℂ) ^ (I * τ) * (n : ℂ) ^ (I * τ) := by
  rw [natCpow_I_mul _ (Nat.mul_pos hm hn), natCpow_I_mul _ hm, natCpow_I_mul _ hn,
    ← Complex.exp_add]
  congr 1
  push_cast
  rw [Real.log_mul (by positivity) (by positivity)]
  push_cast; ring

lemma labelTuples_cons_eq : labelTuples x a = Fintype.piFinset fun i => primeGroup x (a i) := rfl

/-- `𝔅_ρ` as a sum over pairs `(p₀, q)`. -/
lemma Bpoly_eq_pairs (τ : ℝ) :
    Bpoly x a Y lam k ρ τ = ∑ pq ∈ primeGroup x (a 0) ×ˢ
        Fintype.piFinset (fun i : Fin K' => primeGroup x (a i.succ)),
      if ((pq.1 * ∏ i, pq.2 i : ℕ) : ZMod k) = ρ then
        fL lam ((pq.1 * ∏ i, pq.2 i : ℕ) / Y) * ((pq.1 * ∏ i, pq.2 i : ℕ) : ℂ) ^ (I * τ)
      else 0 := by
  unfold Bpoly
  rw [labelTuples_cons_eq, sum_piFinset_cons]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [prod_cons_eq]

lemma pos_of_mem_primeGroup {x y : ℝ} {p : ℕ} (hp : p ∈ primeGroup x y) : 0 < p :=
  (mem_primeGroup_bounds hp).1.pos

lemma prod_pos_of_mem {x : ℝ} {K' : ℕ} {a : Fin K' → ℝ} {q : Fin K' → ℕ}
    (hq : q ∈ Fintype.piFinset fun i => primeGroup x (a i)) : 0 < ∏ i, q i := by
  rw [Fintype.mem_piFinset] at hq
  exact Finset.prod_pos fun i _ => pos_of_mem_primeGroup (hq i)

/-- `Bmain` as a sum over pairs. -/
lemma Bmain_eq_pairs (hδ0 : 0 < δs) (τ : ℝ) :
    Bmain x a Y lam δs k ρ τ = ∑ pq ∈ primeGroup x (a 0) ×ˢ
        Fintype.piFinset (fun i : Fin K' => primeGroup x (a i.succ)),
      if ((pq.1 * ∏ i, pq.2 i : ℕ) : ZMod k) = ρ then
        fL lam (Pj x a δs (jf x a δs pq.1) * (∏ i, pq.2 i : ℕ) / Y) *
          ((pq.1 * ∏ i, pq.2 i : ℕ) : ℂ) ^ (I * τ)
      else 0 := by
  classical
  set Q := Fintype.piFinset (fun i : Fin K' => primeGroup x (a i.succ)) with hQ
  set G : ℕ → ℂ := fun p₀ => ∑ q ∈ Q, if ((p₀ * ∏ i, q i : ℕ) : ZMod k) = ρ then
      fL lam (Pj x a δs (jf x a δs p₀) * (∏ i, q i : ℕ) / Y) *
        ((p₀ * ∏ i, q i : ℕ) : ℂ) ^ (I * τ) else 0 with hG
  rw [Finset.sum_product]
  change _ = ∑ p₀ ∈ primeGroup x (a 0), G p₀
  have hmaps : ∀ p ∈ primeGroup x (a 0), (jf x a δs p, (p : ZMod k)) ∈
      range (Jn x a δs) ×ˢ (Finset.univ : Finset (ZMod k)) := by
    intro p hp
    rw [mem_product, mem_range]
    exact ⟨(jf_bounds x a δs hδ0 hp).1, mem_univ _⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_product]
  unfold Bmain
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => ?_
  -- the fiber is `Spiece`
  have hfib : (primeGroup x (a 0)).filter (fun p => (jf x a δs p, (p : ZMod k)) = (j, u)) =
      Spiece x a δs k j u := by
    unfold Spiece
    congr 1
    funext p
    simp [Prod.ext_iff]
  rw [hfib]
  have hPj : (Pj x a δs j : ℂ) ≠ 0 := by
    unfold Pj Plo; exact_mod_cast (by positivity : (0 : ℝ) < _).ne'
  unfold Pf Rrest
  rw [← mul_assoc, mul_inv_cancel₀ hPj, one_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  unfold Spiece at hp
  rw [mem_filter] at hp
  obtain ⟨hp0, hpj, hpu⟩ := hp
  rw [hG]; simp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hpos0 := pos_of_mem_primeGroup hp0
  have hposq := prod_pos_of_mem hq
  rw [hpj]
  have hres : ((p * ∏ i, q i : ℕ) : ZMod k) = u * ((∏ i, q i : ℕ) : ZMod k) := by
    push_cast; rw [hpu]
  rw [hres]
  split_ifs
  · rw [natCpow_I_mul_mul p _ hpos0 hposq τ]; ring
  · rw [mul_zero]

lemma Spiece_mem (hδ0 : 0 < δs) (hδ1 : δs ≤ 1 / 2) (j : ℕ) (u : ZMod k) :
    ∀ p ∈ Spiece x a δs k j u, p.Prime ∧ Pj x a δs j ≤ p ∧ (p : ℝ) ≤ 2 * Pj x a δs j := by
  intro p hp
  unfold Spiece at hp
  rw [mem_filter] at hp
  obtain ⟨hp0, hpj, _⟩ := hp
  obtain ⟨h1, h2, h3⟩ := jf_bounds x a δs hδ0 hp0
  rw [hpj] at h2 h3
  refine ⟨(mem_primeGroup_bounds hp0).1, h2, ?_⟩
  have he : Real.exp δs ≤ 2 := by
    have := exp_sub_one_le_two_mul δs hδ0.le (by linarith); linarith
  have hP : 0 ≤ Pj x a δs j := by unfold Pj Plo; positivity
  nlinarith

lemma norm_Rrest_le (hY : 0 < Y) (j : ℕ) (u : ZMod k) (τ : ℝ) :
    ‖Rrest x a Y lam δs k ρ j u τ‖ ≤
      4 * Y / Pj x a δs j * ∏ i : Fin K', groupReciprocalSum x (a i.succ) := by
  have hPj : 0 < Pj x a δs j := by unfold Pj Plo; positivity
  unfold Rrest
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ q ∈ Fintype.piFinset (fun i : Fin K' => primeGroup x (a i.succ)),
      ‖if u * ((∏ i, q i : ℕ) : ZMod k) = ρ then
        fL lam (Pj x a δs j * (∏ i, q i : ℕ) / Y) * ((∏ i, q i : ℕ) : ℂ) ^ (I * τ) else 0‖ ≤
      if ((∏ i, q i : ℕ) : ℝ) ≤ 4 * Y / Pj x a δs j then (1 : ℝ) else 0 := by
    intro q hq
    have hposq := prod_pos_of_mem hq
    split_ifs with h1 h2 h2
    · rw [norm_mul, norm_natCpow_I_mul _ hposq, mul_one]; exact norm_fL_le _ _
    · by_contra hne
      push_neg at hne
      rw [norm_mul, norm_natCpow_I_mul _ hposq, mul_one] at hne
      have hne' : fL lam (Pj x a δs j * (∏ i, q i : ℕ) / Y) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hne; exact lt_irrefl _ hne
      have := (fL_ne_zero hne').2
      apply h2
      rw [div_lt_iff₀ hY] at this
      rw [le_div_iff₀ hPj]
      linarith
    · simp
    · simp
  refine (sum_le_sum hpt).trans ?_
  have := card_prod_le (fun i : Fin K' => primeGroup x (a i.succ))
    (fun i p hp => pos_of_mem_primeGroup hp) (4 * Y / Pj x a δs j) (by positivity)
  refine this.trans (le_of_eq ?_)
  rfl


/-- The approximation error. -/
lemma norm_Bpoly_sub_Bmain_le (hδ0 : 0 < δs) (hδ1 : δs ≤ 1 / 2) (hY : 0 < Y) (Lη : ℝ)
    (hLη0 : 0 ≤ Lη) (hLη : ∀ y y' : ℝ, |dyadicBump y - dyadicBump y'| ≤ Lη * |y - y'|)
    (τ : ℝ) :
    ‖Bpoly x a Y lam k ρ τ - Bmain x a Y lam δs k ρ τ‖ ≤
      16 * δs * (Lη + 2 * π * |lam|) * (8 * Y * ∏ i, groupReciprocalSum x (a i)) := by
  set Lip := Lη + 2 * π * |lam| with hLip
  have hLip0 : 0 ≤ Lip := by positivity
  have he : Real.exp δs ≤ 2 := by
    have := exp_sub_one_le_two_mul δs hδ0.le (by linarith); linarith
  have he1 : Real.exp δs - 1 ≤ 2 * δs := exp_sub_one_le_two_mul δs hδ0.le (by linarith)
  rw [Bpoly_eq_pairs, Bmain_eq_pairs x a Y lam δs k ρ hδ0, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ pq ∈ primeGroup x (a 0) ×ˢ Fintype.piFinset (fun i : Fin K' => primeGroup x (a i.succ)),
      ‖(if ((pq.1 * ∏ i, pq.2 i : ℕ) : ZMod k) = ρ then
          fL lam ((pq.1 * ∏ i, pq.2 i : ℕ) / Y) * ((pq.1 * ∏ i, pq.2 i : ℕ) : ℂ) ^ (I * τ)
        else 0) -
        (if ((pq.1 * ∏ i, pq.2 i : ℕ) : ZMod k) = ρ then
          fL lam (Pj x a δs (jf x a δs pq.1) * (∏ i, pq.2 i : ℕ) / Y) *
            ((pq.1 * ∏ i, pq.2 i : ℕ) : ℂ) ^ (I * τ)
        else 0)‖ ≤
      if (((pq.1 * ∏ i, pq.2 i : ℕ) : ℕ) : ℝ) ≤ 8 * Y then 16 * δs * Lip else 0 := by
    intro pq hpq
    rw [mem_product] at hpq
    obtain ⟨hp0, hq⟩ := hpq
    have hpos0 := pos_of_mem_primeGroup hp0
    have hposq := prod_pos_of_mem hq
    obtain ⟨_, hlow, hup⟩ := jf_bounds x a δs hδ0 hp0
    set P' := Pj x a δs (jf x a δs pq.1) with hP'
    have hP'0 : 0 < P' := by rw [hP']; unfold Pj Plo; positivity
    set qq : ℝ := ((∏ i, pq.2 i : ℕ) : ℝ) with hqq
    have hqq0 : 0 < qq := by rw [hqq]; exact_mod_cast hposq
    have hcast : (((pq.1 * ∏ i, pq.2 i : ℕ) : ℕ) : ℝ) = (pq.1 : ℝ) * qq := by
      rw [hqq]; push_cast; ring
    by_cases hres : ((pq.1 * ∏ i, pq.2 i : ℕ) : ZMod k) = ρ
    · rw [if_pos hres, if_pos hres, ← sub_mul, norm_mul,
        norm_natCpow_I_mul _ (Nat.mul_pos hpos0 hposq), mul_one]
      set y := (((pq.1 * ∏ i, pq.2 i : ℕ) : ℕ) : ℝ) / Y with hy
      set y' := P' * qq / Y with hy'
      have hyy : y' ≤ y := by
        rw [hy, hy', hcast]; gcongr
      have hyy2 : y - y' ≤ 2 * δs * y := by
        rw [hy, hy', hcast, ← sub_div, ← sub_mul]
        have : (pq.1 : ℝ) - P' ≤ 2 * δs * pq.1 := by
          have : (pq.1 : ℝ) - P' ≤ P' * (Real.exp δs - 1) := by linarith only [hup]
          have h1 := mul_le_mul_of_nonneg_left he1 hP'0.le
          have h2 := mul_le_mul_of_nonneg_left hlow (show (0 : ℝ) ≤ 2 * δs by linarith only [hδ0])
          linarith only [this, h1, h2]
        rw [mul_div_assoc', mul_assoc]
        apply div_le_div_of_nonneg_right _ hY.le
        have h3 := mul_le_mul_of_nonneg_right this hqq0.le
        linarith only [h3]
      split_ifs with hsm
      · have hy8 : y ≤ 8 := by rw [hy, div_le_iff₀ hY]; linarith
        refine (norm_fL_sub_le Lη hLη lam y y').trans ?_
        rw [abs_of_nonneg (show (0 : ℝ) ≤ y - y' by linarith), ← hLip]
        have : y - y' ≤ 16 * δs := by
          have h4 := mul_le_mul_of_nonneg_left hy8 (show (0 : ℝ) ≤ 2 * δs by linarith only [hδ0])
          linarith only [h4, hyy2]
        calc Lip * (y - y') ≤ Lip * (16 * δs) := by gcongr
          _ = 16 * δs * Lip := by ring
      · push_neg at hsm
        have hy8 : 8 < y := by rw [hy, lt_div_iff₀ hY]; linarith
        have hfy : fL lam y = 0 := by
          by_contra h; have := (fL_ne_zero h).2; linarith
        have hfy' : fL lam y' = 0 := by
          by_contra h
          have := (fL_ne_zero h).2
          have h2 : y ≤ 2 * y' := by
            rw [hy, hy', hcast]
            have : (pq.1 : ℝ) ≤ 2 * P' := by
              have h5 := mul_le_mul_of_nonneg_left he hP'0.le
              linarith only [h5, hup]
            have h6 := mul_le_mul_of_nonneg_right this hqq0.le
            rw [div_le_iff₀ hY]
            field_simp
            linarith only [this, h6]
          linarith
        rw [hfy, hfy', sub_zero, norm_zero]
    · rw [if_neg hres, if_neg hres, sub_zero, norm_zero]
      split_ifs <;> positivity
  refine (sum_le_sum hpt).trans ?_
  -- back to label tuples
  have hback : ∑ pq ∈ primeGroup x (a 0) ×ˢ Fintype.piFinset (fun i : Fin K' => primeGroup x (a i.succ)),
      (if (((pq.1 * ∏ i, pq.2 i : ℕ) : ℕ) : ℝ) ≤ 8 * Y then 16 * δs * Lip else 0) =
      16 * δs * Lip * ∑ p ∈ labelTuples x a,
        (if ((∏ i, p i : ℕ) : ℝ) ≤ 8 * Y then (1 : ℝ) else 0) := by
    rw [mul_sum, labelTuples_cons_eq, sum_piFinset_cons]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rw [prod_cons_eq]
    split_ifs <;> ring
  rw [hback]
  have hcnt := card_prod_le (fun i => primeGroup x (a i)) (fun i p hp => pos_of_mem_primeGroup hp)
    (8 * Y) (by positivity)
  have hcnt' : ∑ p ∈ labelTuples x a, (if ((∏ i, p i : ℕ) : ℝ) ≤ 8 * Y then (1 : ℝ) else 0) ≤
      8 * Y * ∏ i, groupReciprocalSum x (a i) := hcnt
  have : 0 ≤ 16 * δs * Lip := by positivity
  calc 16 * δs * Lip * ∑ p ∈ labelTuples x a, (if ((∏ i, p i : ℕ) : ℝ) ≤ 8 * Y then (1 : ℝ) else 0)
      ≤ 16 * δs * Lip * (8 * Y * ∏ i, groupReciprocalSum x (a i)) := by gcongr


end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the integral bound for `∫ |𝔅 M N|²` through the short-interval decomposition
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

lemma norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  calc ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ s.card * ∑ i ∈ s, ‖z i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

variable (x : ℝ) {K' : ℕ} (a : Fin (K' + 1) → ℝ) (Y lam δs : ℝ) (k : ℕ) [NeZero k] (ρ : ZMod k)

lemma Bpoly_continuous : Continuous (Bpoly x a Y lam k ρ) := by
  unfold Bpoly
  refine continuous_finsetSum _ fun p hp => ?_
  split_ifs
  · have hpos : 0 < ∏ i, p i := by
      unfold labelTuples at hp
      rw [Fintype.mem_piFinset] at hp
      exact Finset.prod_pos fun i _ => pos_of_mem_primeGroup (hp i)
    exact continuous_const.mul (continuous_natCpow_I_mul _ hpos)
  · exact continuous_const

lemma Pf_continuous (𝒮 : Finset ℕ) (h𝒮 : ∀ p ∈ 𝒮, 0 < p) (P : ℝ) : Continuous (Pf 𝒮 P) := by
  unfold Pf
  exact continuous_const.mul (continuous_finsetSum _ fun p hp => continuous_natCpow_I_mul p (h𝒮 p hp))

lemma Spiece_pos (j : ℕ) (u : ZMod k) : ∀ p ∈ Spiece x a δs k j u, 0 < p := by
  intro p hp
  unfold Spiece at hp
  exact pos_of_mem_primeGroup (mem_filter.mp hp).1

/-- **Integral bound through the decomposition.** -/
theorem B_int_bound (hδ0 : 0 < δs) (hδ1 : δs ≤ 1 / 2) (hY : 0 < Y) (Lη : ℝ) (hLη0 : 0 ≤ Lη)
    (hLη : ∀ y y' : ℝ, |dyadicBump y - dyadicBump y'| ≤ Lη * |y - y'|)
    (M N : ℝ → ℂ) (hMc : Continuous M) (hNc : Continuous N) (T₀ : ℝ) (hT₀ : 0 ≤ T₀) :
    ∫ τ in (-T₀)..T₀, ‖Bpoly x a Y lam k ρ τ * M τ * N τ‖ ^ 2 ≤
      2 * ((Jn x a δs * k : ℕ) : ℝ) * (4 * Y * ∏ i : Fin K', groupReciprocalSum x (a i.succ)) ^ 2 *
        (∑ j ∈ range (Jn x a δs), ∑ u : ZMod k, ∫ τ in (-T₀)..T₀,
          ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) +
      2 * (16 * δs * (Lη + 2 * π * |lam|) * (8 * Y * ∏ i, groupReciprocalSum x (a i))) ^ 2 *
        ∫ τ in (-T₀)..T₀, ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 := by
  set E := 16 * δs * (Lη + 2 * π * |lam|) * (8 * Y * ∏ i, groupReciprocalSum x (a i)) with hE
  set W := 4 * Y * ∏ i : Fin K', groupReciprocalSum x (a i.succ) with hW
  set nP : ℝ := ((Jn x a δs * k : ℕ) : ℝ) with hnP
  have hV0 : ∀ i : Fin K', 0 ≤ groupReciprocalSum x (a i.succ) := fun i =>
    Finset.sum_nonneg fun p _ => by positivity
  have hW0 : 0 ≤ W := by rw [hW]; have := Finset.prod_nonneg fun i (_ : i ∈ univ) => hV0 i; positivity
  have hpt : ∀ τ : ℝ, ‖Bpoly x a Y lam k ρ τ * M τ * N τ‖ ^ 2 ≤
      2 * nP * W ^ 2 * ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
        ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 +
      2 * E ^ 2 * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) := by
    intro τ
    set B := Bpoly x a Y lam k ρ τ
    set Bm := Bmain x a Y lam δs k ρ τ
    have hdiff := norm_Bpoly_sub_Bmain_le x a Y lam δs k ρ hδ0 hδ1 hY Lη hLη0 hLη τ
    have hBm : ‖Bm‖ ^ 2 ≤ nP * W ^ 2 * ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
        ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 := by
      have e : Bm = ∑ ju ∈ range (Jn x a δs) ×ˢ (univ : Finset (ZMod k)),
          (Pj x a δs ju.1 : ℂ) * Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ *
            Rrest x a Y lam δs k ρ ju.1 ju.2 τ := by
        rw [Finset.sum_product]; rfl
      rw [e]
      refine (norm_sum_sq_le_card _ _).trans ?_
      have hcard : ((range (Jn x a δs) ×ˢ (univ : Finset (ZMod k))).card : ℝ) = nP := by
        rw [card_product, card_range, card_univ, ZMod.card, hnP]
      rw [hcard]
      have hterm : ∀ ju ∈ range (Jn x a δs) ×ˢ (univ : Finset (ZMod k)),
          ‖(Pj x a δs ju.1 : ℂ) * Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ *
            Rrest x a Y lam δs k ρ ju.1 ju.2 τ‖ ^ 2 ≤
          W ^ 2 * ‖Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ‖ ^ 2 := by
        intro ju _
        have hPj : 0 < Pj x a δs ju.1 := by unfold Pj Plo; positivity
        have hR := norm_Rrest_le x a Y lam δs k ρ hY ju.1 ju.2 τ
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hPj.le, mul_pow, mul_pow]
        have hR2 : ‖Rrest x a Y lam δs k ρ ju.1 ju.2 τ‖ ^ 2 ≤ (W / Pj x a δs ju.1) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          refine hR.trans (le_of_eq ?_)
          rw [hW]; ring
        calc Pj x a δs ju.1 ^ 2 * ‖Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ‖ ^ 2 *
              ‖Rrest x a Y lam δs k ρ ju.1 ju.2 τ‖ ^ 2
            ≤ Pj x a δs ju.1 ^ 2 * ‖Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ‖ ^ 2 *
              (W / Pj x a δs ju.1) ^ 2 := by gcongr
          _ = W ^ 2 * ‖Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ‖ ^ 2 := by
              field_simp
      have hnP0 : 0 ≤ nP := by rw [hnP]; positivity
      calc nP * ∑ ju ∈ range (Jn x a δs) ×ˢ (univ : Finset (ZMod k)),
            ‖(Pj x a δs ju.1 : ℂ) * Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ *
              Rrest x a Y lam δs k ρ ju.1 ju.2 τ‖ ^ 2
          ≤ nP * ∑ ju ∈ range (Jn x a δs) ×ˢ (univ : Finset (ZMod k)),
            W ^ 2 * ‖Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ‖ ^ 2 := by
            gcongr with ju hju; exact hterm ju hju
        _ = nP * W ^ 2 * ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
            ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 := by
            have e3 : ∑ ju ∈ range (Jn x a δs) ×ˢ (univ : Finset (ZMod k)),
                W ^ 2 * ‖Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ‖ ^ 2 =
                W ^ 2 * ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
                  ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 := by
              rw [← Finset.mul_sum]
              congr 1
              exact Finset.sum_product (range (Jn x a δs)) (univ : Finset (ZMod k))
                (fun ju => ‖Pf (Spiece x a δs k ju.1 ju.2) (Pj x a δs ju.1) τ‖ ^ 2)
            rw [e3]; ring
    have hsplit : ‖B‖ ^ 2 ≤ 2 * ‖Bm‖ ^ 2 + 2 * E ^ 2 := by
      have h1 : ‖B‖ ≤ ‖Bm‖ + ‖B - Bm‖ := by
        have := norm_add_le Bm (B - Bm); rwa [add_sub_cancel] at this
      have h2 : ‖B - Bm‖ ≤ E := hdiff
      have h3 : 0 ≤ ‖B - Bm‖ := norm_nonneg _
      have hb2 : ‖B - Bm‖ ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ h3 h2 2
      have ha2 : ‖B‖ ^ 2 ≤ (‖Bm‖ + ‖B - Bm‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith only [sq_nonneg (‖Bm‖ - ‖B - Bm‖), ha2, hb2]
    rw [norm_mul, norm_mul, mul_pow, mul_pow]
    have hMN : 0 ≤ ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 := by positivity
    have e2 : ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
        ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 =
        (∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
          ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2) * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun u _ => ?_
      ring
    rw [e2]
    calc ‖B‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 = ‖B‖ ^ 2 * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) := by ring
      _ ≤ (2 * ‖Bm‖ ^ 2 + 2 * E ^ 2) * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) := by gcongr
      _ ≤ (2 * (nP * W ^ 2 * ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
            ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2) + 2 * E ^ 2) *
            (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) := by gcongr
      _ = _ := by ring
  have hPfc : ∀ j u, Continuous (Pf (Spiece x a δs k j u) (Pj x a δs j)) := fun j u =>
    Pf_continuous _ (Spiece_pos x a δs k j u) _
  have hcont_l : Continuous fun τ => ‖Bpoly x a Y lam k ρ τ * M τ * N τ‖ ^ 2 :=
    (((Bpoly_continuous x a Y lam k ρ).mul hMc).mul hNc).norm.pow 2
  have hcpiece : ∀ j u, Continuous fun τ =>
      ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 := fun j u => by
    have := hPfc j u; fun_prop
  have hcont_r : Continuous fun τ => 2 * nP * W ^ 2 * ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
      ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 +
      2 * E ^ 2 * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2) := by
    refine Continuous.add (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun u _ => hcpiece j u)) ?_
    fun_prop
  calc ∫ τ in (-T₀)..T₀, ‖Bpoly x a Y lam k ρ τ * M τ * N τ‖ ^ 2
      ≤ ∫ τ in (-T₀)..T₀, (2 * nP * W ^ 2 * ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
          ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 +
          2 * E ^ 2 * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2)) :=
        intervalIntegral.integral_mono_on (by linarith) (hcont_l.intervalIntegrable _ _)
          (hcont_r.intervalIntegrable _ _) (fun τ _ => hpt τ)
    _ = _ := by
        have hfin : ∫ τ in (-T₀)..T₀, ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k,
            ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 =
            ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k, ∫ τ in (-T₀)..T₀,
              ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 := by
          rw [intervalIntegral.integral_finsetSum]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [intervalIntegral.integral_finsetSum]
            intro u _; exact (hcpiece j u).intervalIntegrable _ _
          · intro j _
            exact (continuous_finsetSum _ fun u _ => hcpiece j u).intervalIntegrable _ _
        rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, hfin]
        · exact (continuous_const.mul (continuous_finsetSum _ fun j _ =>
            continuous_finsetSum _ fun u _ => hcpiece j u)).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun τ => 2 * E ^ 2 * (‖M τ‖ ^ 2 * ‖N τ‖ ^ 2)).intervalIntegrable _ _

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the endpoint polynomial `U` and its residue decomposition

`U(τ) = ∑_{i} u_i w_i^{iτ}` has `|U(τ)| = |∑_ρ ph(ρ) 𝔅_{ρ₁}(τ) 𝔐_{ρ₂}(τ) 𝔑_{ρ₃}(τ)|`, so
`|U(τ)|² ≤ k³ ∑_ρ |𝔅_{ρ₁} 𝔐_{ρ₂} 𝔑_{ρ₃}|²`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset

noncomputable section

lemma ee_add (u v : ℝ) : ee (u + v) = ee u * ee v := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_mod (c N : ℤ) (k : ℕ) (hk : k ≠ 0) :
    ee (c * (N : ℝ) / k) = ee (c * (((N : ZMod k).val : ℕ) : ℝ) / k) := by
  haveI : NeZero k := ⟨hk⟩
  have hv : (((N : ZMod k).val : ℕ) : ℤ) = N % (k : ℤ) := by
    rw [ZMod.val_intCast]
  have hdecomp : N = N % (k : ℤ) + (k : ℤ) * (N / (k : ℤ)) := (Int.emod_add_mul_ediv N k).symm
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have e : c * (N : ℝ) / k = c * (((N : ZMod k).val : ℕ) : ℝ) / k + ((c * (N / (k : ℤ)) : ℤ) : ℝ) := by
    have h1 : ((((N : ZMod k).val : ℕ) : ℤ) : ℝ) = ((N % (k : ℤ) : ℤ) : ℝ) := by rw [hv]
    have h2 : (N : ℝ) = ((N % (k : ℤ) : ℤ) : ℝ) + (k : ℝ) * ((N / (k : ℤ) : ℤ) : ℝ) := by
      conv_lhs => rw [hdecomp]
      push_cast; ring
    push_cast at h1 ⊢
    rw [h2, ← h1]
    field_simp
  rw [e, ee_add, ee_int, mul_one]

/-- The residue phase `ph(ρ) = e(c (ρ₁ρ₂ρ₃ - ρ₁)/k)`. -/
def ph (c : ℤ) (k : ℕ) (ρ : ZMod k × ZMod k × ZMod k) : ℂ :=
  ee (c * (((ρ.1 * ρ.2.1 * ρ.2.2 - ρ.1 : ZMod k).val : ℕ) : ℝ) / k)

lemma norm_ph (c : ℤ) (k : ℕ) (ρ : ZMod k × ZMod k × ZMod k) : ‖ph c k ρ‖ = 1 := norm_ee _

/-- The natural-number form of `U`. -/
def UU (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (c : ℤ) (k : ℕ) (lam τ : ℝ) : ℂ :=
  ∑ i ∈ Ix x a Hm Hn, uco Y α β c k lam i * ((bP i * i.2.1 * i.2.2 : ℕ) : ℂ) ^ (I * τ)

lemma bP_pos {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {i : (Fin K → ℕ) × ℕ × ℕ}
    (hi : i.1 ∈ labelTuples x a) : 0 < bP i := by
  unfold labelTuples at hi
  rw [Fintype.mem_piFinset] at hi
  unfold bP
  exact Finset.prod_pos fun j _ => (mem_primeGroup_bounds (hi j)).1.pos

/-- **Residue decomposition of `U`.** -/
lemma UU_eq (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (c : ℤ) (k : ℕ) [NeZero k] (lam τ : ℝ) :
    UU x a Y Hm Hn α β c k lam τ = ∑ ρ : ZMod k × ZMod k × ZMod k, ph c k ρ *
      (Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ) := by
  have hk : k ≠ 0 := NeZero.ne k
  -- pointwise identity
  have hpt : ∀ i ∈ Ix x a Hm Hn, uco Y α β c k lam i * ((bP i * i.2.1 * i.2.2 : ℕ) : ℂ) ^ (I * τ) =
      ∑ ρ : ZMod k × ZMod k × ZMod k, ph c k ρ *
        ((if ((bP i : ℕ) : ZMod k) = ρ.1 then fL lam ((bP i : ℕ) / Y) * ((bP i : ℕ) : ℂ) ^ (I * τ)
            else 0) *
         (if ((i.2.1 : ℕ) : ZMod k) = ρ.2.1 then α i.2.1 * ((i.2.1 : ℕ) : ℂ) ^ (I * τ) else 0) *
         (if ((i.2.2 : ℕ) : ZMod k) = ρ.2.2 then β i.2.2 * ((i.2.2 : ℕ) : ℂ) ^ (I * τ) else 0)) := by
    intro i hi
    have hb := bP_pos (mem_product.mp hi).1
    have hsum : ∀ (F : ZMod k × ZMod k × ZMod k → ℂ),
        ∑ ρ : ZMod k × ZMod k × ZMod k, F ρ *
          ((if ((bP i : ℕ) : ZMod k) = ρ.1 then (1 : ℂ) else 0) *
           (if ((i.2.1 : ℕ) : ZMod k) = ρ.2.1 then (1 : ℂ) else 0) *
           (if ((i.2.2 : ℕ) : ZMod k) = ρ.2.2 then (1 : ℂ) else 0)) =
        F (((bP i : ℕ) : ZMod k), ((i.2.1 : ℕ) : ZMod k), ((i.2.2 : ℕ) : ZMod k)) := by
      intro F
      rw [Finset.sum_eq_single (((bP i : ℕ) : ZMod k), ((i.2.1 : ℕ) : ZMod k),
        ((i.2.2 : ℕ) : ZMod k))]
      · simp
      · intro ρ _ hne
        have : ¬ (((bP i : ℕ) : ZMod k) = ρ.1 ∧ ((i.2.1 : ℕ) : ZMod k) = ρ.2.1 ∧
            ((i.2.2 : ℕ) : ZMod k) = ρ.2.2) := by
          rintro ⟨h1, h2, h3⟩; apply hne; ext <;> simp [h1, h2, h3]
        by_cases h1 : ((bP i : ℕ) : ZMod k) = ρ.1
        · by_cases h2 : ((i.2.1 : ℕ) : ZMod k) = ρ.2.1
          · have h3 : ¬ ((i.2.2 : ℕ) : ZMod k) = ρ.2.2 := fun h3 => this ⟨h1, h2, h3⟩
            simp [h3]
          · simp [h2]
        · simp [h1]
      · intro h; exact absurd (mem_univ _) h
    have e1 : ∀ ρ : ZMod k × ZMod k × ZMod k, ph c k ρ *
        ((if ((bP i : ℕ) : ZMod k) = ρ.1 then fL lam ((bP i : ℕ) / Y) * ((bP i : ℕ) : ℂ) ^ (I * τ)
            else 0) *
         (if ((i.2.1 : ℕ) : ZMod k) = ρ.2.1 then α i.2.1 * ((i.2.1 : ℕ) : ℂ) ^ (I * τ) else 0) *
         (if ((i.2.2 : ℕ) : ZMod k) = ρ.2.2 then β i.2.2 * ((i.2.2 : ℕ) : ℂ) ^ (I * τ) else 0)) =
        (ph c k ρ * (fL lam ((bP i : ℕ) / Y) * ((bP i : ℕ) : ℂ) ^ (I * τ) *
          (α i.2.1 * ((i.2.1 : ℕ) : ℂ) ^ (I * τ)) * (β i.2.2 * ((i.2.2 : ℕ) : ℂ) ^ (I * τ)))) *
          ((if ((bP i : ℕ) : ZMod k) = ρ.1 then (1 : ℂ) else 0) *
           (if ((i.2.1 : ℕ) : ZMod k) = ρ.2.1 then (1 : ℂ) else 0) *
           (if ((i.2.2 : ℕ) : ZMod k) = ρ.2.2 then (1 : ℂ) else 0)) := by
      intro ρ
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun ρ _ => e1 ρ]
    rw [hsum (fun ρ => ph c k ρ * (fL lam ((bP i : ℕ) / Y) * ((bP i : ℕ) : ℂ) ^ (I * τ) *
          (α i.2.1 * ((i.2.1 : ℕ) : ℂ) ^ (I * τ)) * (β i.2.2 * ((i.2.2 : ℕ) : ℂ) ^ (I * τ))))]
    -- the phase
    have hph : ph c k (((bP i : ℕ) : ZMod k), ((i.2.1 : ℕ) : ZMod k), ((i.2.2 : ℕ) : ZMod k)) =
        ee (c * (((bP i * i.2.1 * i.2.2 : ℕ) : ℝ) - (bP i : ℝ)) / k) := by
      unfold ph
      have := ee_mod c (((bP i * i.2.1 * i.2.2 : ℕ) : ℤ) - (bP i : ℤ)) k hk
      push_cast at this ⊢
      rw [this]
    rw [hph]
    unfold uco
    by_cases hm : i.2.1 = 0
    · rw [hm, hα0]; simp
    by_cases hn : i.2.2 = 0
    · rw [hn, hβ0]; simp
    have hm' : 0 < i.2.1 := Nat.pos_of_ne_zero hm
    have hn' : 0 < i.2.2 := Nat.pos_of_ne_zero hn
    rw [show (bP i * i.2.1 * i.2.2 : ℕ) = bP i * (i.2.1 * i.2.2) by ring,
      natCpow_I_mul_mul _ _ hb (Nat.mul_pos hm' hn'), natCpow_I_mul_mul _ _ hm' hn']
    ring
  unfold UU
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold Ix Bpoly Rpoly bP
  rw [Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul, Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]

/-- `|U|² ≤ k³ ∑_ρ |𝔅𝔐𝔑|²`. -/
lemma norm_UU_sq_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (c : ℤ) (k : ℕ) [NeZero k] (lam τ : ℝ) :
    ‖UU x a Y Hm Hn α β c k lam τ‖ ^ 2 ≤ (k : ℝ) ^ 3 * ∑ ρ : ZMod k × ZMod k × ZMod k,
      ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 := by
  rw [UU_eq x a Y Hm Hn α β hα0 hβ0 c k lam τ]
  refine (norm_sum_sq_le_card _ _).trans ?_
  have hc : ((Finset.univ : Finset (ZMod k × ZMod k × ZMod k)).card : ℝ) = (k : ℝ) ^ 3 := by
    rw [card_univ, Fintype.card_prod, Fintype.card_prod, ZMod.card]; push_cast; ring
  rw [hc]
  gcongr with ρ _
  rw [norm_mul, norm_ph, one_mul]

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the pointwise bound for the arc integrand

For `θ = c/k + λ/Y`, `‖G(θ)‖ ≤ ∏V⁻² K (1+|λ|)⁴ (ε k⁶ M_U + k⁶ M_V / ε)/(4X)` whenever every
residue piece satisfies `∫ ω_X |𝔅𝔐𝔑|² ≤ M_U` and `∫ ω_X(τ) |𝔅𝔐𝔑(τ - σ)|² dτ ≤ M_V`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset MeasureTheory

noncomputable section

lemma ωX_eq_ωa (X : ℝ) : ωX X = ωa (2 * π * X) := rfl

lemma uco_ne_zero_supp {K : ℕ} {Y : ℝ} {α β : ℕ → ℂ} {c : ℤ} {k : ℕ} {lam : ℝ}
    {i : (Fin K → ℕ) × ℕ × ℕ} (h : uco Y α β c k lam i ≠ 0) :
    fL lam (bP i / Y) ≠ 0 ∧ α i.2.1 ≠ 0 ∧ β i.2.2 ≠ 0 := by
  unfold uco at h
  refine ⟨?_, ?_, ?_⟩ <;> intro h0 <;> apply h <;> rw [h0] <;> ring

/-- Weights of the support lie in `[1, 16]`. -/
lemma wco_mem {K : ℕ} {Y Hm Hn : ℝ} (hY : 0 < Y) (hHm : 0 < Hm) (hHn : 0 < Hn)
    {α β : ℕ → ℂ} (hα : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm)
    (hβ : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn) {c : ℤ} {k : ℕ} {lam : ℝ}
    {i : (Fin K → ℕ) × ℕ × ℕ} (h : uco Y α β c k lam i ≠ 0) :
    1 ≤ wco (Hm * Hn) Y i ∧ wco (Hm * Hn) Y i ≤ 16 := by
  obtain ⟨h1, h2, h3⟩ := uco_ne_zero_supp h
  have hb := fL_ne_zero h1
  obtain ⟨hm1, hm2⟩ := hα _ h2
  obtain ⟨hn1, hn2⟩ := hβ _ h3
  have hb1 : Y < (bP i : ℝ) := by rw [lt_div_iff₀ hY] at hb; linarith [hb.1]
  have hb2 : (bP i : ℝ) < 4 * Y := by rw [div_lt_iff₀ hY] at hb; linarith [hb.2]
  unfold wco
  have hXY : 0 < Hm * Hn * Y := by positivity
  push_cast
  constructor
  · rw [le_div_iff₀ (by positivity), one_mul]
    have : Hm * Hn ≤ (i.2.1 : ℝ) * i.2.2 := mul_le_mul hm1 hn1 hHn.le (by linarith)
    have h4 : Y * (Hm * Hn) ≤ (bP i : ℝ) * ((i.2.1 : ℝ) * i.2.2) :=
      mul_le_mul hb1.le this (by positivity) (by positivity)
    calc Hm * Hn * Y = Y * (Hm * Hn) := by ring
      _ ≤ _ := h4
      _ = _ := by ring
  · rw [div_le_iff₀ (by positivity)]
    have : (i.2.1 : ℝ) * i.2.2 ≤ (2 * Hm) * (2 * Hn) := mul_le_mul hm2 hn2 (by positivity) (by linarith)
    have h4 : (bP i : ℝ) * ((i.2.1 : ℝ) * i.2.2) ≤ (4 * Y) * ((2 * Hm) * (2 * Hn)) :=
      mul_le_mul hb2.le this (by positivity) (by positivity)
    calc (bP i : ℝ) * i.2.1 * i.2.2 = (bP i : ℝ) * ((i.2.1 : ℝ) * i.2.2) := by ring
      _ ≤ _ := h4
      _ = 16 * (Hm * Hn * Y) := by ring

/-- `dpoly` over the support equals `UU` up to a unimodular factor. -/
lemma norm_dpoly_eq {K : ℕ} (x : ℝ) (a : Fin K → ℝ) {Y Hm Hn : ℝ} (hY : 0 < Y) (hHm : 0 < Hm)
    (hHn : 0 < Hn) {α β : ℕ → ℂ} (hα : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm)
    (hβ : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn) (c : ℤ) (k : ℕ) (lam τ : ℝ) :
    ‖dpoly ((Ix x a Hm Hn).filter fun i => uco Y α β c k lam i ≠ 0) (uco Y α β c k lam)
      (wco (Hm * Hn) Y) τ‖ = ‖UU x a Y Hm Hn α β c k lam τ‖ := by
  have hXY : 0 < Hm * Hn * Y := by positivity
  have e : dpoly ((Ix x a Hm Hn).filter fun i => uco Y α β c k lam i ≠ 0) (uco Y α β c k lam)
      (wco (Hm * Hn) Y) τ = Complex.exp (-(I * τ * Real.log (Hm * Hn * Y))) *
        UU x a Y Hm Hn α β c k lam τ := by
    unfold dpoly UU
    rw [Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_filter_of_ne (p := fun i => uco Y α β c k lam i ≠ 0)
      (fun i _ h => by intro h0; apply h; rw [h0, zero_mul, mul_zero])]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_filter] at hi
    obtain ⟨hiIx, hu⟩ := hi
    obtain ⟨_, h2, h3⟩ := uco_ne_zero_supp hu
    have hm : 0 < i.2.1 := by
      have := (hα _ h2).1
      have : (0 : ℝ) < i.2.1 := lt_of_lt_of_le hHm this
      exact_mod_cast this
    have hn : 0 < i.2.2 := by
      have := (hβ _ h3).1
      have : (0 : ℝ) < i.2.2 := lt_of_lt_of_le hHn this
      exact_mod_cast this
    have hb := bP_pos (mem_product.mp hiIx).1
    have hv : 0 < bP i * i.2.1 * i.2.2 := Nat.mul_pos (Nat.mul_pos hb hm) hn
    have hv' : (0 : ℝ) < ((bP i * i.2.1 * i.2.2 : ℕ) : ℝ) := by exact_mod_cast hv
    rw [natCpow_I_mul _ hv]
    unfold wco
    rw [Real.log_div hv'.ne' hXY.ne']
    have : Complex.exp (I * τ * ((Real.log ((bP i * i.2.1 * i.2.2 : ℕ) : ℝ) -
        Real.log (Hm * Hn * Y) : ℝ) : ℂ)) =
        Complex.exp (-(I * τ * Real.log (Hm * Hn * Y))) *
          Complex.exp (I * τ * Real.log ((bP i * i.2.1 * i.2.2 : ℕ) : ℝ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [e, norm_mul]
  have : ‖Complex.exp (-(I * τ * Real.log (Hm * Hn * Y)))‖ = 1 := by
    rw [show -(I * (τ : ℂ) * ((Real.log (Hm * Hn * Y) : ℝ) : ℂ)) =
      ((-(τ * Real.log (Hm * Hn * Y)) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [this, one_mul]

lemma Rpoly_continuous (H : ℝ) (c : ℕ → ℂ) (hc0 : c 0 = 0) (k : ℕ) (ρ : ZMod k) :
    Continuous (Rpoly H c k ρ) := by
  unfold Rpoly
  refine continuous_finsetSum _ fun m _ => ?_
  split_ifs
  · rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [hc0]; exact continuous_const
    · exact continuous_const.mul (continuous_natCpow_I_mul m h)
  · exact continuous_const

lemma norm_Rpoly_le (H : ℝ) (c : ℕ → ℂ) (hc0 : c 0 = 0) (k : ℕ) (ρ : ZMod k) (τ : ℝ) :
    ‖Rpoly H c k ρ τ‖ ≤ ∑ m ∈ Finset.range (⌊2 * H⌋₊ + 1), ‖c m‖ := by
  unfold Rpoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  split_ifs
  · rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp [hc0]
    · rw [norm_mul, norm_natCpow_I_mul m h, mul_one]
  · simp

lemma norm_Bpoly_le' (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y lam : ℝ) (k : ℕ) (ρ : ZMod k) (τ : ℝ) :
    ‖Bpoly x a Y lam k ρ τ‖ ≤ (labelTuples x a).card := by
  unfold Bpoly
  refine (norm_sum_le _ _).trans ?_
  have : ∀ p ∈ labelTuples x a, ‖if ((∏ i, p i : ℕ) : ZMod k) = ρ then
      fL lam ((∏ i, p i : ℕ) / Y) * ((∏ i, p i : ℕ) : ℂ) ^ (I * τ) else 0‖ ≤ 1 := by
    intro p hp
    have hpos : 0 < ∏ i, p i := by
      unfold labelTuples at hp
      rw [Fintype.mem_piFinset] at hp
      exact Finset.prod_pos fun i _ => (mem_primeGroup_bounds (hp i)).1.pos
    split_ifs
    · rw [norm_mul, norm_natCpow_I_mul _ hpos, mul_one]; exact norm_fL_le _ _
    · simp
  refine (Finset.sum_le_sum this).trans ?_
  simp

lemma Bpoly_continuous' (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y lam : ℝ) (k : ℕ) (ρ : ZMod k) :
    Continuous (Bpoly x a Y lam k ρ) := by
  unfold Bpoly
  refine continuous_finsetSum _ fun p hp => ?_
  split_ifs
  · have hpos : 0 < ∏ i, p i := by
      unfold labelTuples at hp
      rw [Fintype.mem_piFinset] at hp
      exact Finset.prod_pos fun i _ => (mem_primeGroup_bounds (hp i)).1.pos
    exact continuous_const.mul (continuous_natCpow_I_mul _ hpos)
  · exact continuous_const

lemma integrable_ωX_mul (X : ℝ) (hX : 0 < X) (f : ℝ → ℂ) (hf : Continuous f) (B : ℝ)
    (hB : ∀ τ, ‖f τ‖ ≤ B) : Integrable (fun τ => ωX X τ * ‖f τ‖ ^ 2) := by
  rw [ωX_eq_ωa]
  refine (integrable_ωa _ (by positivity)).mul_bdd (c := B ^ 2) (hf.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun τ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hB τ) 2

/-- **The pointwise bound for the arc integrand.** -/
theorem Gth_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (hY : 0 < Y) (hHm : 0 < Hm)
    (hHn : 0 < Hn) (α β : ℕ → ℂ) (hα : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm)
    (hβ : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (lam : ℝ) (c : ℤ) (k : ℕ) [NeZero k] (Ksep : ℝ) (F : ℝ × ℝ → ℂ) (hFc : Continuous F)
    (hFb : ∀ q : ℝ × ℝ, ‖F q‖ ≤ Ksep / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2)))
    (hrep : ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
        psiL lam ((Hm * Hn) * (w - w')) = ∫ q : ℝ × ℝ, F q *
          Complex.exp (2 * π * I * (q.1 * ((Hm * Hn : ℝ) : ℂ) * Real.log w +
            (q.2 - ((Hm * Hn : ℝ) : ℂ) * q.1) * Real.log w')))
    (MU MV ε : ℝ) (hε : 0 < ε)
    (hU : ∀ ρ : ZMod k × ZMod k × ZMod k, ∫ τ, ωX (Hm * Hn) τ *
      ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 ≤ MU)
    (hV : ∀ ρ : ZMod k × ZMod k × ZMod k, ∀ σ : ℝ, ∫ τ, ωX (Hm * Hn) τ *
      ‖Bpoly x a Y lam k ρ.1 (τ - σ) * Rpoly Hm α k ρ.2.1 (τ - σ) *
        Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2 ≤ MV) :
    ‖Gth x a Y Hm Hn α β ((c : ℝ) / k + lam / Y)‖ ≤
      squareNorm x a * (Ksep * (ε * ((k : ℝ) ^ 6 * MU) + (k : ℝ) ^ 6 * MV / ε) /
        (4 * (Hm * Hn))) := by
  have hk : k ≠ 0 := NeZero.ne k
  have hX : 0 < Hm * Hn := by positivity
  have hsq : 0 ≤ squareNorm x a := by
    unfold squareNorm
    exact Finset.prod_nonneg fun i _ => by
      have : 0 ≤ groupReciprocalSum x (a i) := Finset.sum_nonneg fun p _ => by positivity
      positivity
  rw [Gth_eq_form x a Y Hm Hn α β lam c k hY.ne' hX.ne' hk, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hsq]
  gcongr
  set S := (Ix x a Hm Hn).filter fun i => uco Y α β c k lam i ≠ 0 with hS
  have hfilt : ∑ i ∈ Ix x a Hm Hn, ∑ j ∈ Ix x a Hm Hn,
      uco Y α β c k lam i * (starRingEnd ℂ) (uco Y α β c k lam j) *
        psiL lam ((Hm * Hn) * (wco (Hm * Hn) Y i - wco (Hm * Hn) Y j)) =
      ∑ i ∈ S, ∑ j ∈ S, uco Y α β c k lam i * (starRingEnd ℂ) (uco Y α β c k lam j) *
        psiL lam ((Hm * Hn) * (wco (Hm * Hn) Y i - wco (Hm * Hn) Y j)) := by
    rw [hS, Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_filter_of_ne]
      intro j _ h h0; apply h; rw [h0]; simp
    · intro i _ h h0; apply h
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h0]; ring
  rw [hfilt]
  have hw : ∀ i ∈ S, 1 ≤ wco (Hm * Hn) Y i ∧ wco (Hm * Hn) Y i ≤ 16 := by
    intro i hi
    rw [hS, mem_filter] at hi
    exact wco_mem hY hHm hHn hα hβ hi.2
  -- continuity and bounds for the pieces
  have hpc : ∀ ρ : ZMod k × ZMod k × ZMod k, Continuous fun τ =>
      Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ := fun ρ =>
    ((Bpoly_continuous' x a Y lam k ρ.1).mul (Rpoly_continuous Hm α hα0 k ρ.2.1)).mul
      (Rpoly_continuous Hn β hβ0 k ρ.2.2)
  set B₀ := ((labelTuples x a).card : ℝ) * (∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ‖α m‖) *
    (∑ m ∈ Finset.range (⌊2 * Hn⌋₊ + 1), ‖β m‖) with hB₀
  have hpb : ∀ ρ : ZMod k × ZMod k × ZMod k, ∀ τ,
      ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ≤ B₀ := by
    intro ρ τ
    rw [norm_mul, norm_mul, hB₀]
    gcongr
    · exact norm_Bpoly_le' x a Y lam k ρ.1 τ
    · exact norm_Rpoly_le Hm α hα0 k ρ.2.1 τ
    · exact norm_Rpoly_le Hn β hβ0 k ρ.2.2 τ
  have hcardk : ((Finset.univ : Finset (ZMod k × ZMod k × ZMod k)).card : ℝ) = (k : ℝ) ^ 3 := by
    rw [card_univ, Fintype.card_prod, Fintype.card_prod, ZMod.card]; push_cast; ring
  have hUU : ∀ σ : ℝ, ∫ τ, ωX (Hm * Hn) τ * ‖dpoly S (uco Y α β c k lam) (wco (Hm * Hn) Y) (τ - σ)‖ ^ 2 ≤
      (k : ℝ) ^ 3 * ∑ ρ : ZMod k × ZMod k × ZMod k, ∫ τ, ωX (Hm * Hn) τ *
        ‖Bpoly x a Y lam k ρ.1 (τ - σ) * Rpoly Hm α k ρ.2.1 (τ - σ) *
          Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2 := by
    intro σ
    have hint : ∀ ρ : ZMod k × ZMod k × ZMod k, Integrable fun τ => ωX (Hm * Hn) τ *
        ‖Bpoly x a Y lam k ρ.1 (τ - σ) * Rpoly Hm α k ρ.2.1 (τ - σ) *
          Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2 := fun ρ =>
      integrable_ωX_mul _ hX _ ((hpc ρ).comp (continuous_id.sub continuous_const)) B₀
        (fun τ => hpb ρ (τ - σ))
    rw [← integral_finsetSum _ fun ρ _ => hint ρ, ← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun τ => mul_nonneg (ωX_pos _ _).le (sq_nonneg _)
    · exact (integrable_finsetSum _ fun ρ _ => hint ρ).const_mul _
    · refine Filter.Eventually.of_forall fun τ => ?_
      simp only
      rw [norm_dpoly_eq x a hY hHm hHn hα hβ c k lam (τ - σ), Finset.mul_sum]
      have := norm_UU_sq_le x a Y Hm Hn α β hα0 hβ0 c k lam (τ - σ)
      have hω := (ωX_pos (Hm * Hn) τ).le
      calc ωX (Hm * Hn) τ * ‖UU x a Y Hm Hn α β c k lam (τ - σ)‖ ^ 2
          ≤ ωX (Hm * Hn) τ * ((k : ℝ) ^ 3 * ∑ ρ : ZMod k × ZMod k × ZMod k,
            ‖Bpoly x a Y lam k ρ.1 (τ - σ) * Rpoly Hm α k ρ.2.1 (τ - σ) *
              Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2) := by gcongr
        _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun ρ _ => ?_; ring
  have hk3 : (0 : ℝ) ≤ (k : ℝ) ^ 3 := by positivity
  have hMU : ∫ τ, ωX (Hm * Hn) τ * ‖dpoly S (uco Y α β c k lam) (wco (Hm * Hn) Y) τ‖ ^ 2 ≤
      (k : ℝ) ^ 6 * MU := by
    have h0 := hUU 0
    simp only [sub_zero] at h0
    refine h0.trans ?_
    calc (k : ℝ) ^ 3 * ∑ ρ : ZMod k × ZMod k × ZMod k, ∫ τ, ωX (Hm * Hn) τ *
          ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2
        ≤ (k : ℝ) ^ 3 * ∑ _ρ : ZMod k × ZMod k × ZMod k, MU := by gcongr with ρ; exact hU ρ
      _ = (k : ℝ) ^ 6 * MU := by rw [sum_const, nsmul_eq_mul, hcardk]; ring
  have hMV : ∀ σ : ℝ, ∫ τ, ωX (Hm * Hn) τ *
      ‖dpoly S (uco Y α β c k lam) (wco (Hm * Hn) Y) (τ - σ)‖ ^ 2 ≤ (k : ℝ) ^ 6 * MV := by
    intro σ
    refine (hUU σ).trans ?_
    calc (k : ℝ) ^ 3 * ∑ ρ : ZMod k × ZMod k × ZMod k, ∫ τ, ωX (Hm * Hn) τ *
          ‖Bpoly x a Y lam k ρ.1 (τ - σ) * Rpoly Hm α k ρ.2.1 (τ - σ) *
            Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2
        ≤ (k : ℝ) ^ 3 * ∑ _ρ : ZMod k × ZMod k × ZMod k, MV := by gcongr with ρ; exact hV ρ σ
      _ = (k : ℝ) ^ 6 * MV := by rw [sum_const, nsmul_eq_mul, hcardk]; ring
  have := bilinear_bound (Hm * Hn) lam Ksep hX F hFc hFb hrep S S (uco Y α β c k lam)
    (uco Y α β c k lam) (wco (Hm * Hn) Y) (wco (Hm * Hn) Y) hw hw ((k : ℝ) ^ 6 * MU)
    ((k : ℝ) ^ 6 * MV) ε hε hMU hMV
  exact this

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinBV

open Finset

/-- The harmonic sum over `(0, X]`. -/
theorem harm_le (X : ℕ) : ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Icc 1 X = Ioc 0 X := by ext i; simp; omega
  rw [this] at h
  simpa [one_div] using h

theorem harmonic_partial_sum_nonneg (X : ℕ) : 0 ≤ ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) :=
  Finset.sum_nonneg fun i _ => by positivity

/-- `∑_{a,b ≤ X} gcd(a,b)/(ab) ≤ H_X^3`. -/
theorem sum_gcd_div_le (X : ℕ) :
    ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X, ((Nat.gcd a b : ℝ) / (a * b)) ≤
      (∑ i ∈ Ioc 0 X, (1 / (i : ℝ))) ^ 3 := by
  rw [← Finset.sum_product']
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2,
    p.2 / Nat.gcd p.1 p.2) with hφ
  have hinj : Set.InjOn φ ↑(Ioc 0 X ×ˢ Ioc 0 X) := by
    rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have ea : a = Nat.gcd a b * (a / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have eb : b = Nat.gcd a b * (b / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    have ea' : a' = Nat.gcd a' b' * (a' / Nat.gcd a' b') :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left a' b')).symm
    have eb' : b' = Nat.gcd a' b' * (b' / Nat.gcd a' b') :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right a' b')).symm
    simp only [Prod.mk.injEq]
    constructor
    · rw [ea, ea']; exact congrArg₂ (· * ·) h1 h2
    · rw [eb, eb']; exact congrArg₂ (· * ·) h1 h3
  have hval : ∀ p ∈ Ioc 0 X ×ˢ Ioc 0 X, ((Nat.gcd p.1 p.2 : ℝ) / (p.1 * p.2)) =
      (fun t : ℕ × ℕ × ℕ => 1 / ((t.1 : ℝ) * t.2.1 * t.2.2)) (φ p) := by
    rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, Finset.mem_Ioc] at hp
    simp only [hφ]
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ hp.1.1
    have ea : (a : ℝ) = Nat.gcd a b * ((a / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have eb : (b : ℝ) = Nat.gcd a b * ((b / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    have ha0 : ((a / Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, mul_zero] at ea; exact (Nat.pos_iff_ne_zero.mp hp.1.1) (by exact_mod_cast ea)
    have hb0 : ((b / Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, mul_zero] at eb; exact (Nat.pos_iff_ne_zero.mp hp.2.1) (by exact_mod_cast eb)
    have hg0 : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    rw [ea, eb]
    field_simp
  rw [Finset.sum_congr rfl hval,
    ← Finset.sum_image (f := fun t : ℕ × ℕ × ℕ => 1 / ((t.1 : ℝ) * t.2.1 * t.2.2)) hinj]
  have hsub : (Ioc 0 X ×ˢ Ioc 0 X).image φ ⊆ Ioc 0 X ×ˢ Ioc 0 X ×ˢ Ioc 0 X := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_Ioc] at ht ⊢
    obtain ⟨⟨a, b⟩, ⟨⟨ha, haX⟩, hb, hbX⟩, rfl⟩ := ht
    simp only [hφ]
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
    refine ⟨⟨hg, (Nat.gcd_le_left _ ha).trans haX⟩, ⟨?_, (Nat.div_le_self _ _).trans haX⟩, ?_,
      (Nat.div_le_self _ _).trans hbX⟩
    · exact Nat.div_pos (Nat.gcd_le_left _ ha) hg
    · exact Nat.div_pos (Nat.gcd_le_right _ hb) hg
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => by positivity)).trans
    (le_of_eq ?_)
  have : ∀ t ∈ Ioc 0 X ×ˢ Ioc 0 X ×ˢ Ioc 0 X, 1 / ((t.1 : ℝ) * t.2.1 * t.2.2) =
      (1 / (t.1 : ℝ)) * ((1 / (t.2.1 : ℝ)) * (1 / (t.2.2 : ℝ))) := by
    intro t _; rw [one_div_mul_one_div, one_div_mul_one_div, mul_assoc]
  rw [Finset.sum_congr rfl this, Finset.sum_product]
  simp_rw [Finset.sum_product, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **Second moment of the divisor function**: `∑_{n ≤ X} d(n)^2 ≤ X (1 + log X)^3`. -/
theorem sum_card_divisors_sq_le (X : ℕ) :
    ∑ n ∈ Ioc 0 X, ((n.divisors.card : ℝ)) ^ 2 ≤ X * (1 + Real.log X) ^ 3 := by
  have hdiv : ∀ n ∈ Ioc 0 X, ((n.divisors.card : ℝ)) ^ 2 =
      ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hd : n.divisors = (Ioc 0 X).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨h, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hn.1, (Nat.le_of_dvd hn.1 h).trans hn.2⟩, h⟩
      · rintro ⟨-, h⟩
        exact ⟨h, hn.1.ne'⟩
    rw [hd, sq, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;> simp [ha, hb]
  rw [Finset.sum_congr rfl hdiv, Finset.sum_comm]
  have hinner : ∀ a ∈ Ioc 0 X, ∑ n ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X,
      (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) ≤
        ∑ b ∈ Ioc 0 X, (X : ℝ) * (Nat.gcd a b / (a * b)) := by
    intro a ha
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [Finset.mem_Ioc] at ha hb
    have hcount : ∑ n ∈ Ioc 0 X, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) =
        ((X / Nat.lcm a b : ℕ) : ℝ) := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [Nat.lcm_dvd_iff]
      split_ifs <;> simp
    rw [hcount]
    have hl : 0 < Nat.lcm a b := Nat.lcm_pos ha.1 hb.1
    have h1 : ((X / Nat.lcm a b : ℕ) : ℝ) ≤ (X : ℝ) / Nat.lcm a b := Nat.cast_div_le
    have h2 : (X : ℝ) / Nat.lcm a b = X * (Nat.gcd a b / (a * b)) := by
      have := Nat.gcd_mul_lcm a b
      have hab : (a : ℝ) * b = Nat.gcd a b * Nat.lcm a b := by exact_mod_cast this.symm
      rw [hab]
      have : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left _ ha.1).ne'
      have : (Nat.lcm a b : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
      field_simp
    linarith
  refine (Finset.sum_le_sum hinner).trans ?_
  simp_rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_gcd_div_le X).trans ?_) (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (harmonic_partial_sum_nonneg X) (harm_le X) 3

end ArtinBV
end

section
/-!
# L102M: the product polynomial `𝔐𝔑` and its mean values

`𝔐_ρ(τ)𝔑_σ(τ)` is a Dirichlet polynomial in `u = mn ≤ N₄ = ⌊2H_m⌋⌊2H_n⌋` whose coefficients
satisfy `∑_u |c_u|² ≤ B⁴ N₄ (1 + log N₄)³` when `|α|, |β| ≤ B` (divisor bound). Hence the
interval and weighted mean value bounds, also for shifts `τ ↦ τ - σ`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset MeasureTheory

noncomputable section

lemma regroup {ι : Type*} (s : Finset ι) (g : ι → ℕ) (c : ι → ℂ) (τ : ℝ) :
    ∑ i ∈ s, c i * (g i : ℂ) ^ (I * τ) =
      ∑ n ∈ s.image g, (∑ i ∈ s.filter (fun i => g i = n), c i) * (n : ℂ) ^ (I * τ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := s.image g)
    (fun i hi => mem_image_of_mem _ hi)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(mem_filter.mp hi).2]

/-- Regrouped mean value theorem. -/
lemma mvt_gen {ι : Type*} (s : Finset ι) (g : ι → ℕ) (N : ℕ)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ N) (c : ι → ℂ) (T₁ T₂ : ℝ) (hT : T₁ ≤ T₂) :
    ∫ τ in T₁..T₂, ‖∑ i ∈ s, c i * (g i : ℂ) ^ (I * τ)‖ ^ 2 ≤
      (T₂ - T₁ + 4 * N * (1 + Real.log N)) *
        ∑ n ∈ s.image g, ‖∑ i ∈ s.filter (fun i => g i = n), c i‖ ^ 2 := by
  classical
  simp_rw [regroup s g c]
  apply mvt (s.image g) N _ _ T₁ T₂ hT
  intro n hn
  rw [mem_image] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  exact hg i hi

/-- Regrouped weighted mean value theorem. -/
lemma wmvt_gen {ι : Type*} (s : Finset ι) (g : ι → ℕ) (N : ℕ)
    (hg : ∀ i ∈ s, 1 ≤ g i ∧ g i ≤ N) (c : ι → ℂ) (a : ℝ) (ha : 0 < a) :
    ∫ τ, ωa a τ * ‖∑ i ∈ s, c i * (g i : ℂ) ^ (I * τ)‖ ^ 2 ≤
      (Real.pi * a + 2 * Real.pi * N * (1 + Real.log N)) *
        ∑ n ∈ s.image g, ‖∑ i ∈ s.filter (fun i => g i = n), c i‖ ^ 2 := by
  classical
  simp_rw [regroup s g c]
  apply wmvt (s.image g) N _ _ a ha
  intro n hn
  rw [mem_image] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  exact hg i hi

/-- The divisor bound for product coefficients. -/
lemma sum_fiber_pairs_le (A B' : Finset ℕ) (hA : ∀ m ∈ A, 1 ≤ m) (hB : ∀ n ∈ B', 1 ≤ n)
    (N : ℕ) (hN : ∀ m ∈ A, ∀ n ∈ B', m * n ≤ N) (c : ℕ × ℕ → ℂ) (Bd : ℝ)
    (hc : ∀ i, ‖c i‖ ≤ Bd) :
    ∑ u ∈ (A ×ˢ B').image (fun i => i.1 * i.2),
      ‖∑ i ∈ (A ×ˢ B').filter (fun i => i.1 * i.2 = u), c i‖ ^ 2 ≤
      Bd ^ 2 * (N * (1 + Real.log N) ^ 3) := by
  classical
  have hBd : 0 ≤ Bd := le_trans (norm_nonneg _) (hc (0, 0))
  have hfib : ∀ u ∈ (A ×ˢ B').image (fun i => i.1 * i.2),
      ‖∑ i ∈ (A ×ˢ B').filter (fun i => i.1 * i.2 = u), c i‖ ^ 2 ≤
        Bd ^ 2 * ((u.divisors.card : ℝ)) ^ 2 := by
    intro u hu
    have hcard : ((A ×ˢ B').filter (fun i => i.1 * i.2 = u)).card ≤ u.divisors.card := by
      have hu0 : u ≠ 0 := by
        rw [mem_image] at hu
        obtain ⟨i, hi, rfl⟩ := hu
        rw [mem_product] at hi
        exact Nat.mul_ne_zero (by have := hA _ hi.1; omega) (by have := hB _ hi.2; omega)
      apply Finset.card_le_card_of_injOn (fun i => i.1)
      · intro i hi
        rw [mem_coe, mem_filter] at hi
        rw [mem_coe, Nat.mem_divisors]
        exact ⟨⟨i.2, hi.2.symm⟩, hu0⟩
      · intro i hi j hj hij
        rw [mem_coe, mem_filter] at hi hj
        simp only at hij
        have h1 := hi.2; have h2 := hj.2
        have hpos : 0 < i.1 := by have := hA _ (mem_product.mp hi.1).1; omega
        have : i.2 = j.2 := by
          rw [hij] at h1
          have hpos' : 0 < j.1 := by rw [← hij]; exact hpos
          exact Nat.eq_of_mul_eq_mul_left hpos' (h1.trans h2.symm)
        exact Prod.ext hij this
    calc ‖∑ i ∈ (A ×ˢ B').filter (fun i => i.1 * i.2 = u), c i‖ ^ 2
        ≤ (((A ×ˢ B').filter (fun i => i.1 * i.2 = u)).card * Bd) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans ?_
          calc ∑ i ∈ (A ×ˢ B').filter (fun i => i.1 * i.2 = u), ‖c i‖
              ≤ ∑ i ∈ (A ×ˢ B').filter (fun i => i.1 * i.2 = u), Bd := sum_le_sum fun i _ => hc i
            _ = _ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ((u.divisors.card : ℝ) * Bd) ^ 2 := by
          gcongr
      _ = Bd ^ 2 * ((u.divisors.card : ℝ)) ^ 2 := by ring
  have hsub : (A ×ˢ B').image (fun i => i.1 * i.2) ⊆ Ioc 0 N := by
    intro u hu
    rw [mem_image] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    rw [mem_product] at hi
    rw [mem_Ioc]
    exact ⟨Nat.mul_pos (by have := hA _ hi.1; omega) (by have := hB _ hi.2; omega),
      hN _ hi.1 _ hi.2⟩
  calc ∑ u ∈ (A ×ˢ B').image (fun i => i.1 * i.2),
        ‖∑ i ∈ (A ×ˢ B').filter (fun i => i.1 * i.2 = u), c i‖ ^ 2
      ≤ ∑ u ∈ (A ×ˢ B').image (fun i => i.1 * i.2), Bd ^ 2 * ((u.divisors.card : ℝ)) ^ 2 :=
        sum_le_sum hfib
    _ ≤ ∑ u ∈ Ioc 0 N, Bd ^ 2 * ((u.divisors.card : ℝ)) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = Bd ^ 2 * ∑ u ∈ Ioc 0 N, ((u.divisors.card : ℝ)) ^ 2 := by rw [mul_sum]
    _ ≤ Bd ^ 2 * (N * (1 + Real.log N) ^ 3) := by
        gcongr; exact ArtinBV.sum_card_divisors_sq_le N

/-- Positive integers up to `2H`. -/
def Apos (H : ℝ) : Finset ℕ := (Finset.range (⌊2 * H⌋₊ + 1)).filter (1 ≤ ·)

/-- The product coefficients. -/
def MNco (α β : ℕ → ℂ) (k : ℕ) (ρ₂ ρ₃ : ZMod k) (i : ℕ × ℕ) : ℂ :=
  (if (i.1 : ZMod k) = ρ₂ then α i.1 else 0) * (if (i.2 : ZMod k) = ρ₃ then β i.2 else 0)

lemma Rpoly_eq_Apos (H : ℝ) (c : ℕ → ℂ) (hc0 : c 0 = 0) (k : ℕ) (ρ : ZMod k) (τ : ℝ) :
    Rpoly H c k ρ τ = ∑ m ∈ Apos H, (if (m : ZMod k) = ρ then c m else 0) * (m : ℂ) ^ (I * τ) := by
  unfold Rpoly Apos
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : 1 ≤ m
  · rw [if_pos hm]; split_ifs <;> simp
  · have : m = 0 := by omega
    subst this; simp [hc0]

lemma Rpoly_mul_eq (Hm Hn : ℝ) (α β : ℕ → ℂ) (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (k : ℕ)
    (ρ₂ ρ₃ : ZMod k) (τ : ℝ) :
    Rpoly Hm α k ρ₂ τ * Rpoly Hn β k ρ₃ τ =
      ∑ i ∈ Apos Hm ×ˢ Apos Hn, MNco α β k ρ₂ ρ₃ i * ((i.1 * i.2 : ℕ) : ℂ) ^ (I * τ) := by
  rw [Rpoly_eq_Apos Hm α hα0, Rpoly_eq_Apos Hn β hβ0, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  have hm1 : 0 < m := by unfold Apos at hm; rw [mem_filter] at hm; omega
  have hn1 : 0 < n := by unfold Apos at hn; rw [mem_filter] at hn; omega
  unfold MNco
  rw [natCpow_I_mul_mul m n hm1 hn1]
  ring

lemma norm_MNco_le (α β : ℕ → ℂ) (Bα Bβ : ℝ) (hα : ∀ m, ‖α m‖ ≤ Bα) (hβ : ∀ n, ‖β n‖ ≤ Bβ)
    (k : ℕ) (ρ₂ ρ₃ : ZMod k) (i : ℕ × ℕ) : ‖MNco α β k ρ₂ ρ₃ i‖ ≤ Bα * Bβ := by
  unfold MNco
  have hBα : 0 ≤ Bα := le_trans (norm_nonneg _) (hα 0)
  rw [norm_mul]
  apply mul_le_mul _ _ (norm_nonneg _) hBα
  · split_ifs
    · exact hα _
    · simpa using hBα
  · split_ifs
    · exact hβ _
    · simpa using le_trans (norm_nonneg _) (hβ 0)

lemma Apos_prod_bounds (Hm Hn : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) :
    ∀ i ∈ Apos Hm ×ˢ Apos Hn, 1 ≤ i.1 * i.2 ∧ i.1 * i.2 ≤ ⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ := by
  intro i hi
  rw [mem_product] at hi
  unfold Apos at hi
  rw [mem_filter, mem_filter, mem_range, mem_range] at hi
  exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    Nat.mul_le_mul (by omega) (by omega)⟩

/-- **Interval mean value for `𝔐𝔑`.** -/
theorem MN_int_le (Hm Hn : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (α β : ℕ → ℂ) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (Bα Bβ : ℝ) (hα : ∀ m, ‖α m‖ ≤ Bα) (hβ : ∀ n, ‖β n‖ ≤ Bβ) (k : ℕ)
    (ρ₂ ρ₃ : ZMod k) (T₁ T₂ : ℝ) (hT : T₁ ≤ T₂) :
    ∫ τ in T₁..T₂, ‖Rpoly Hm α k ρ₂ τ * Rpoly Hn β k ρ₃ τ‖ ^ 2 ≤
      (T₂ - T₁ + 4 * (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) * (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ))) *
        ((Bα * Bβ) ^ 2 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
          (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ)) ^ 3)) := by
  simp_rw [Rpoly_mul_eq Hm Hn α β hα0 hβ0 k ρ₂ ρ₃]
  have hm := mvt_gen (Apos Hm ×ˢ Apos Hn) (fun i : ℕ × ℕ => i.1 * i.2) (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊)
    (Apos_prod_bounds Hm Hn hHm hHn) (MNco α β k ρ₂ ρ₃) T₁ T₂ hT
  refine le_trans hm ?_
  have hlog : 0 ≤ 1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) := by
    rcases Nat.eq_zero_or_pos (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊) with h | h
    · rw [h]; simp
    · have : (1 : ℝ) ≤ (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) := by exact_mod_cast h
      linarith [Real.log_nonneg this]
  gcongr
  exact sum_fiber_pairs_le _ _ (fun m hm => by unfold Apos at hm; rw [mem_filter] at hm; exact hm.2)
    (fun n hn => by unfold Apos at hn; rw [mem_filter] at hn; exact hn.2) _
    (fun m hm n hn => (Apos_prod_bounds Hm Hn hHm hHn (m, n) (mem_product.mpr ⟨hm, hn⟩)).2)
    _ _ (norm_MNco_le α β Bα Bβ hα hβ k ρ₂ ρ₃)

/-- **Weighted mean value for shifted `𝔐𝔑`.** -/
theorem MN_wint_le (Hm Hn : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (α β : ℕ → ℂ) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (Bα Bβ : ℝ) (hα : ∀ m, ‖α m‖ ≤ Bα) (hβ : ∀ n, ‖β n‖ ≤ Bβ) (k : ℕ)
    (ρ₂ ρ₃ : ZMod k) (a : ℝ) (ha : 0 < a) (σ : ℝ) :
    ∫ τ, ωa a τ * ‖Rpoly Hm α k ρ₂ (τ - σ) * Rpoly Hn β k ρ₃ (τ - σ)‖ ^ 2 ≤
      (Real.pi * a + 2 * Real.pi * (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
        (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ))) *
        ((Bα * Bβ) ^ 2 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
          (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ)) ^ 3)) := by
  have hshift : ∀ τ, Rpoly Hm α k ρ₂ (τ - σ) * Rpoly Hn β k ρ₃ (τ - σ) =
      ∑ i ∈ Apos Hm ×ˢ Apos Hn, (MNco α β k ρ₂ ρ₃ i * ((i.1 * i.2 : ℕ) : ℂ) ^ (I * (-σ : ℝ))) *
        ((i.1 * i.2 : ℕ) : ℂ) ^ (I * τ) := by
    intro τ
    rw [Rpoly_mul_eq Hm Hn α β hα0 hβ0 k ρ₂ ρ₃]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hpos : 0 < i.1 * i.2 := (Apos_prod_bounds Hm Hn hHm hHn i hi).1
    rw [mul_assoc, natCpow_I_mul_add _ hpos, show (-σ + τ : ℝ) = τ - σ by ring]
  simp_rw [hshift]
  have hm := wmvt_gen (Apos Hm ×ˢ Apos Hn) (fun i : ℕ × ℕ => i.1 * i.2) (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊)
    (Apos_prod_bounds Hm Hn hHm hHn)
    (fun i => MNco α β k ρ₂ ρ₃ i * ((i.1 * i.2 : ℕ) : ℂ) ^ (I * (-σ : ℝ))) a ha
  refine le_trans hm ?_
  have hlog : 0 ≤ 1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) := by
    rcases Nat.eq_zero_or_pos (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊) with h | h
    · rw [h]; simp
    · have : (1 : ℝ) ≤ (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) := by exact_mod_cast h
      linarith [Real.log_nonneg this]
  gcongr
  refine sum_fiber_pairs_le _ _ (fun m hm => by unfold Apos at hm; rw [mem_filter] at hm; exact hm.2)
    (fun n hn => by unfold Apos at hn; rw [mem_filter] at hn; exact hn.2) _
    (fun m hm n hn => (Apos_prod_bounds Hm Hn hHm hHn (m, n) (mem_product.mpr ⟨hm, hn⟩)).2)
    _ _ (fun i => ?_)
  rcases Nat.eq_zero_or_pos (i.1 * i.2) with h | h
  · rw [h]
    by_cases hσ : I * ((-σ : ℝ) : ℂ) = 0
    · rw [hσ, Complex.cpow_zero, mul_one]; exact norm_MNco_le α β Bα Bβ hα hβ k ρ₂ ρ₃ i
    · simp only [Nat.cast_zero, Complex.zero_cpow hσ, mul_zero, norm_zero]
      exact mul_nonneg (le_trans (norm_nonneg _) (hα 0)) (le_trans (norm_nonneg _) (hβ 0))
  · rw [norm_mul, norm_natCpow_I_mul _ h, mul_one]
    exact norm_MNco_le α β Bα Bβ hα hβ k ρ₂ ρ₃ i

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the two mean-square inputs `M_U`, `M_V` of the bilinear bound, per residue class

* `MV_bound`: `∫ ω_X(τ) |𝔅𝔐𝔑(τ - σ)|² ≤ (4Y∏V)² · (weighted mean value of 𝔐𝔑)`.
* `MU_bound`: `∫ ω_X |𝔅𝔐𝔑|² ≤ ∫_{-T₀}^{T₀} |𝔅𝔐𝔑|² + 2(2πX/T₀)² (4Y∏V)² · (weighted mean
  value of 𝔐𝔑 at scale T₀)`, and the first term through the decomposition (5.21).
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset MeasureTheory

noncomputable section

lemma norm_Bpoly_le4 (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y lam : ℝ) (hY : 0 < Y) (k : ℕ)
    (ρ : ZMod k) (τ : ℝ) :
    ‖Bpoly x a Y lam k ρ τ‖ ≤ 4 * Y * ∏ i, groupReciprocalSum x (a i) := by
  unfold Bpoly
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ p ∈ labelTuples x a, ‖if ((∏ i, p i : ℕ) : ZMod k) = ρ then
      fL lam ((∏ i, p i : ℕ) / Y) * ((∏ i, p i : ℕ) : ℂ) ^ (I * τ) else 0‖ ≤
      if ((∏ i, p i : ℕ) : ℝ) ≤ 4 * Y then (1 : ℝ) else 0 := by
    intro p hp
    have hpos : 0 < ∏ i, p i := by
      unfold labelTuples at hp
      rw [Fintype.mem_piFinset] at hp
      exact Finset.prod_pos fun i _ => (mem_primeGroup_bounds (hp i)).1.pos
    split_ifs with h1 h2 h2
    · rw [norm_mul, norm_natCpow_I_mul _ hpos, mul_one]; exact norm_fL_le _ _
    · rw [norm_mul, norm_natCpow_I_mul _ hpos, mul_one]
      by_contra hne
      push_neg at hne
      have hne' : fL lam ((∏ i, p i : ℕ) / Y) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hne; exact lt_irrefl _ hne
      have := (fL_ne_zero hne').2
      apply h2
      rw [div_lt_iff₀ hY] at this
      linarith
    · simp
    · simp
  refine (sum_le_sum hpt).trans ?_
  exact card_prod_le (fun i => primeGroup x (a i)) (fun i p hp => (mem_primeGroup_bounds hp).1.pos)
    (4 * Y) (by positivity)

lemma ωX_le_split (X T₀ : ℝ) (hX : 0 < X) (hT : 2 * π * X ≤ T₀) (τ : ℝ) :
    ωX X τ ≤ (Set.Icc (-T₀) T₀).indicator (fun _ => (1 : ℝ)) τ +
      2 * (2 * π * X / T₀) ^ 2 * ωa T₀ τ := by
  have hT0 : 0 < T₀ := lt_of_lt_of_le (by positivity) hT
  have hω : 0 ≤ ωa T₀ τ := (ωa_pos _ _).le
  by_cases h : τ ∈ Set.Icc (-T₀) T₀
  · rw [Set.indicator_of_mem h]
    have := ωX_le_one X τ
    have : 0 ≤ 2 * (2 * π * X / T₀) ^ 2 * ωa T₀ τ := by positivity
    linarith
  · rw [Set.indicator_of_notMem h, zero_add]
    have hτ : T₀ < |τ| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have hτ2 : T₀ ^ 2 < τ ^ 2 := by
      rw [← sq_abs τ]; exact pow_lt_pow_left₀ hτ hT0.le (by norm_num)
    have hτpos : 0 < τ ^ 2 := lt_trans (pow_pos hT0 2) hτ2
    unfold ωX ωa
    set a := 2 * π * X with ha
    have ha0 : 0 < a := by rw [ha]; positivity
    simp only [div_pow]
    have h1 : (1 + τ ^ 2 / a ^ 2)⁻¹ ≤ a ^ 2 / τ ^ 2 := by
      rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]
      have : τ ^ 2 / a ^ 2 ≤ 1 + τ ^ 2 / a ^ 2 := by linarith
      exact this
    have h2 : T₀ ^ 2 / (2 * τ ^ 2) ≤ (1 + τ ^ 2 / T₀ ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by positivity) (by positivity), inv_div]
      have h3 : 1 ≤ τ ^ 2 / T₀ ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      have e : 2 * τ ^ 2 / T₀ ^ 2 = 2 * (τ ^ 2 / T₀ ^ 2) := by ring
      rw [e]; linarith
    calc (1 + τ ^ 2 / a ^ 2)⁻¹ ≤ a ^ 2 / τ ^ 2 := h1
      _ = 2 * (a ^ 2 / T₀ ^ 2) * (T₀ ^ 2 / (2 * τ ^ 2)) := by field_simp
      _ ≤ 2 * (a ^ 2 / T₀ ^ 2) * (1 + τ ^ 2 / T₀ ^ 2)⁻¹ := by gcongr

lemma int_ωX_split (X T₀ : ℝ) (hX : 0 < X) (hT : 2 * π * X ≤ T₀) (f : ℝ → ℝ)
    (hfc : Continuous f) (hf0 : ∀ τ, 0 ≤ f τ) (B : ℝ) (hfB : ∀ τ, f τ ≤ B) :
    ∫ τ, ωX X τ * f τ ≤ (∫ τ in (-T₀)..T₀, f τ) +
      2 * (2 * π * X / T₀) ^ 2 * ∫ τ, ωa T₀ τ * f τ := by
  have hT0 : 0 < T₀ := lt_of_lt_of_le (by positivity) hT
  have hB0 : 0 ≤ B := le_trans (hf0 0) (hfB 0)
  have hint1 : Integrable fun τ => (Set.Icc (-T₀) T₀).indicator (fun _ => (1 : ℝ)) τ * f τ := by
    have : (fun τ => (Set.Icc (-T₀) T₀).indicator (fun _ => (1 : ℝ)) τ * f τ) =
        (Set.Icc (-T₀) T₀).indicator f := by
      funext τ; by_cases h : τ ∈ Set.Icc (-T₀) T₀
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    rw [this, integrable_indicator_iff measurableSet_Icc]
    exact hfc.integrableOn_Icc
  have hint2 : Integrable fun τ => ωa T₀ τ * f τ :=
    (integrable_ωa T₀ hT0).mul_bdd (c := B) hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => by rw [Real.norm_of_nonneg (hf0 τ)]; exact hfB τ)
  calc ∫ τ, ωX X τ * f τ
      ≤ ∫ τ, ((Set.Icc (-T₀) T₀).indicator (fun _ => (1 : ℝ)) τ * f τ +
          2 * (2 * π * X / T₀) ^ 2 * (ωa T₀ τ * f τ)) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun τ => mul_nonneg (ωX_pos _ _).le (hf0 τ)
        · exact hint1.add (hint2.const_mul _)
        · refine Filter.Eventually.of_forall fun τ => ?_
          have := ωX_le_split X T₀ hX hT τ
          have h0 := hf0 τ
          calc ωX X τ * f τ ≤ ((Set.Icc (-T₀) T₀).indicator (fun _ => (1 : ℝ)) τ +
                2 * (2 * π * X / T₀) ^ 2 * ωa T₀ τ) * f τ := by gcongr
            _ = _ := by ring
    _ = (∫ τ in (-T₀)..T₀, f τ) + 2 * (2 * π * X / T₀) ^ 2 * ∫ τ, ωa T₀ τ * f τ := by
        rw [integral_add hint1 (hint2.const_mul _), integral_const_mul]
        congr 1
        rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
          ← integral_indicator measurableSet_Icc]
        congr 1; funext τ
        by_cases h : τ ∈ Set.Icc (-T₀) T₀
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- The `V`-side (trivial) mean square, per residue class. -/
theorem MV_bound (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y lam : ℝ) (hY : 0 < Y) (k : ℕ)
    (ρ : ZMod k × ZMod k × ZMod k) (Hm Hn : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (α β : ℕ → ℂ)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (Bα Bβ : ℝ) (hα : ∀ m, ‖α m‖ ≤ Bα) (hβ : ∀ n, ‖β n‖ ≤ Bβ)
    (X : ℝ) (hX : 0 < X) (σ : ℝ) :
    ∫ τ, ωX X τ * ‖Bpoly x a Y lam k ρ.1 (τ - σ) * Rpoly Hm α k ρ.2.1 (τ - σ) *
      Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2 ≤
      (4 * Y * ∏ i, groupReciprocalSum x (a i)) ^ 2 *
        ((Real.pi * (2 * π * X) + 2 * Real.pi * (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
          (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ))) *
          ((Bα * Bβ) ^ 2 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
            (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ)) ^ 3))) := by
  set W4 := 4 * Y * ∏ i, groupReciprocalSum x (a i) with hW4
  have hMNc : Continuous fun τ => Rpoly Hm α k ρ.2.1 (τ - σ) * Rpoly Hn β k ρ.2.2 (τ - σ) :=
    ((Rpoly_continuous Hm α hα0 k ρ.2.1).mul (Rpoly_continuous Hn β hβ0 k ρ.2.2)).comp
      (continuous_id.sub continuous_const)
  have hMNb : ∀ τ, ‖Rpoly Hm α k ρ.2.1 (τ - σ) * Rpoly Hn β k ρ.2.2 (τ - σ)‖ ≤
      (∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ‖α m‖) * (∑ m ∈ Finset.range (⌊2 * Hn⌋₊ + 1), ‖β m‖) := by
    intro τ; rw [norm_mul]
    exact mul_le_mul (norm_Rpoly_le Hm α hα0 k _ _) (norm_Rpoly_le Hn β hβ0 k _ _)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hint : Integrable fun τ => ωX X τ *
      ‖Rpoly Hm α k ρ.2.1 (τ - σ) * Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2 :=
    integrable_ωX_mul X hX _ hMNc _ hMNb
  calc ∫ τ, ωX X τ * ‖Bpoly x a Y lam k ρ.1 (τ - σ) * Rpoly Hm α k ρ.2.1 (τ - σ) *
        Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2
      ≤ ∫ τ, W4 ^ 2 * (ωX X τ * ‖Rpoly Hm α k ρ.2.1 (τ - σ) * Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun τ => mul_nonneg (ωX_pos _ _).le (sq_nonneg _)
        · exact hint.const_mul _
        · refine Filter.Eventually.of_forall fun τ => ?_
          have hB := norm_Bpoly_le4 x a Y lam hY k ρ.1 (τ - σ)
          have hω := (ωX_pos X τ).le
          dsimp only
          rw [mul_assoc (Bpoly x a Y lam k ρ.1 (τ - σ)), norm_mul, mul_pow]
          calc ωX X τ * (‖Bpoly x a Y lam k ρ.1 (τ - σ)‖ ^ 2 *
                ‖Rpoly Hm α k ρ.2.1 (τ - σ) * Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2)
              ≤ ωX X τ * (W4 ^ 2 * ‖Rpoly Hm α k ρ.2.1 (τ - σ) * Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2) := by
                gcongr
            _ = _ := by ring
    _ = W4 ^ 2 * ∫ τ, ωX X τ * ‖Rpoly Hm α k ρ.2.1 (τ - σ) * Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2 :=
        integral_const_mul _ _
    _ ≤ _ := by
        gcongr
        rw [ωX_eq_ωa]
        exact MN_wint_le Hm Hn hHm hHn α β hα0 hβ0 Bα Bβ hα hβ k ρ.2.1 ρ.2.2 _ (by positivity) σ

/-- The `U`-side mean square, split at `T₀`. -/
theorem MU_split (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y lam : ℝ) (hY : 0 < Y) (k : ℕ)
    (ρ : ZMod k × ZMod k × ZMod k) (Hm Hn : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (α β : ℕ → ℂ)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (Bα Bβ : ℝ) (hα : ∀ m, ‖α m‖ ≤ Bα) (hβ : ∀ n, ‖β n‖ ≤ Bβ)
    (X T₀ : ℝ) (hX : 0 < X) (hT : 2 * π * X ≤ T₀) :
    ∫ τ, ωX X τ * ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 ≤
      (∫ τ in (-T₀)..T₀, ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ *
        Rpoly Hn β k ρ.2.2 τ‖ ^ 2) +
      2 * (2 * π * X / T₀) ^ 2 * ((4 * Y * ∏ i, groupReciprocalSum x (a i)) ^ 2 *
        ((Real.pi * T₀ + 2 * Real.pi * (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
          (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ))) *
          ((Bα * Bβ) ^ 2 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
            (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ)) ^ 3)))) := by
  have hT0 : 0 < T₀ := lt_of_lt_of_le (by positivity) hT
  set W4 := 4 * Y * ∏ i, groupReciprocalSum x (a i) with hW4
  set B₀ := ((labelTuples x a).card : ℝ) * (∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ‖α m‖) *
    (∑ m ∈ Finset.range (⌊2 * Hn⌋₊ + 1), ‖β m‖) with hB₀
  have hfc : Continuous fun τ =>
      ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 :=
    ((((Bpoly_continuous' x a Y lam k ρ.1).mul (Rpoly_continuous Hm α hα0 k ρ.2.1)).mul
      (Rpoly_continuous Hn β hβ0 k ρ.2.2)).norm).pow 2
  have hfb : ∀ τ, ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 ≤
      B₀ ^ 2 := by
    intro τ
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul, norm_mul, hB₀]
    gcongr
    · exact norm_Bpoly_le' x a Y lam k ρ.1 τ
    · exact norm_Rpoly_le Hm α hα0 k ρ.2.1 τ
    · exact norm_Rpoly_le Hn β hβ0 k ρ.2.2 τ
  refine (int_ωX_split X T₀ hX hT _ hfc (fun τ => sq_nonneg _) _ hfb).trans ?_
  gcongr
  have hMN := MV_bound x a Y lam hY k ρ Hm Hn hHm hHn α β hα0 hβ0 Bα Bβ hα hβ
  -- reuse the argument of `MV_bound` at scale `T₀` and shift `0`
  have hMNc : Continuous fun τ => Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ :=
    (Rpoly_continuous Hm α hα0 k ρ.2.1).mul (Rpoly_continuous Hn β hβ0 k ρ.2.2)
  have hMNb : ∀ τ, ‖Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ≤
      (∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ‖α m‖) * (∑ m ∈ Finset.range (⌊2 * Hn⌋₊ + 1), ‖β m‖) := by
    intro τ; rw [norm_mul]
    exact mul_le_mul (norm_Rpoly_le Hm α hα0 k _ _) (norm_Rpoly_le Hn β hβ0 k _ _)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hint : Integrable fun τ => ωa T₀ τ * ‖Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 :=
    (integrable_ωa T₀ hT0).mul_bdd (c := ((∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1), ‖α m‖) *
      (∑ m ∈ Finset.range (⌊2 * Hn⌋₊ + 1), ‖β m‖)) ^ 2) (hMNc.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hMNb τ) 2)
  calc ∫ τ, ωa T₀ τ * ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2
      ≤ ∫ τ, W4 ^ 2 * (ωa T₀ τ * ‖Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun τ => mul_nonneg (ωa_pos _ _).le (sq_nonneg _)
        · exact hint.const_mul _
        · refine Filter.Eventually.of_forall fun τ => ?_
          have hB := norm_Bpoly_le4 x a Y lam hY k ρ.1 τ
          have hω := (ωa_pos T₀ τ).le
          dsimp only
          rw [mul_assoc (Bpoly x a Y lam k ρ.1 τ), norm_mul, mul_pow]
          calc ωa T₀ τ * (‖Bpoly x a Y lam k ρ.1 τ‖ ^ 2 *
                ‖Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2)
              ≤ ωa T₀ τ * (W4 ^ 2 * ‖Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2) := by
                gcongr
            _ = _ := by ring
    _ = W4 ^ 2 * ∫ τ, ωa T₀ τ * ‖Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 :=
        integral_const_mul _ _
    _ ≤ _ := by
        gcongr
        have := MN_wint_le Hm Hn hHm hHn α β hα0 hβ0 Bα Bβ hα hβ k ρ.2.1 ρ.2.2 T₀ hT0 0
        simp only [sub_zero] at this
        exact this

/-- **(5.21) assembly**: the decomposition plus a per-piece bound. -/
theorem bound_521 (x : ℝ) {K' : ℕ} (a : Fin (K' + 1) → ℝ) (Y lam δs : ℝ) (k : ℕ) [NeZero k]
    (ρ : ZMod k) (hδ0 : 0 < δs) (hδ1 : δs ≤ 1 / 2) (hY : 0 < Y) (Lη : ℝ) (hLη0 : 0 ≤ Lη)
    (hLη : ∀ y y' : ℝ, |dyadicBump y - dyadicBump y'| ≤ Lη * |y - y'|)
    (M N : ℝ → ℂ) (hMc : Continuous M) (hNc : Continuous N) (T₀ : ℝ) (hT₀ : 0 ≤ T₀) (Q : ℝ)
    (hQ : ∀ j ∈ range (Jn x a δs), ∀ u : ZMod k, ∫ τ in (-T₀)..T₀,
      ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 ≤ Q) :
    ∫ τ in (-T₀)..T₀, ‖Bpoly x a Y lam k ρ τ * M τ * N τ‖ ^ 2 ≤
      2 * ((Jn x a δs * k : ℕ) : ℝ) * (4 * Y * ∏ i : Fin K', groupReciprocalSum x (a i.succ)) ^ 2 *
        (((Jn x a δs * k : ℕ) : ℝ) * Q) +
      2 * (16 * δs * (Lη + 2 * π * |lam|) * (8 * Y * ∏ i, groupReciprocalSum x (a i))) ^ 2 *
        ∫ τ in (-T₀)..T₀, ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 := by
  refine (B_int_bound x a Y lam δs k ρ hδ0 hδ1 hY Lη hLη0 hLη M N hMc hNc T₀ hT₀).trans ?_
  gcongr
  calc ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k, ∫ τ in (-T₀)..T₀,
        ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2
      ≤ ∑ j ∈ range (Jn x a δs), ∑ u : ZMod k, Q :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun u _ => hQ j hj u
    _ = ((Jn x a δs * k : ℕ) : ℝ) * Q := by
        rw [Finset.sum_const, Finset.sum_const, card_univ, ZMod.card, card_range]
        simp [nsmul_eq_mul]; ring

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: normalized forms of the mean-square inputs and of the arc bound
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset MeasureTheory

noncomputable section

lemma N4_le (Hm Hn : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) :
    ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) ≤ 4 * (Hm * Hn) := by
  push_cast
  have h1 : (⌊2 * Hm⌋₊ : ℝ) ≤ 2 * Hm := Nat.floor_le (by positivity)
  have h2 : (⌊2 * Hn⌋₊ : ℝ) ≤ 2 * Hn := Nat.floor_le (by positivity)
  calc (⌊2 * Hm⌋₊ : ℝ) * ⌊2 * Hn⌋₊ ≤ (2 * Hm) * (2 * Hn) :=
        mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
    _ = 4 * (Hm * Hn) := by ring

lemma logN4_le (Hm Hn L : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (hL : 1 ≤ L)
    (hlog : Real.log (4 * (Hm * Hn)) ≤ 2 * L) :
    0 ≤ 1 + Real.log ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) ∧
      1 + Real.log ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) ≤ 3 * L := by
  rcases Nat.eq_zero_or_pos (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊) with h | h
  · rw [h]; simp; linarith
  · have h1 : (1 : ℝ) ≤ ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
    have h2 := Real.log_le_log (by linarith) (N4_le Hm Hn hHm hHn)
    constructor
    · linarith [Real.log_nonneg h1]
    · linarith

lemma rpow_C_sq (L C : ℝ) (hL : 0 < L) : (L ^ C * L ^ C) ^ 2 = L ^ (4 * C) := by
  rw [← Real.rpow_add hL, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  push_cast; ring_nf

/-- The `V`-side, normalized. -/
lemma MV_norm (L Hm Hn C : ℝ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (hL : 1 ≤ L)
    (hlog : Real.log (4 * (Hm * Hn)) ≤ 2 * L) :
    (Real.pi * (2 * π * (Hm * Hn)) + 2 * Real.pi * (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
      (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ))) *
      ((L ^ C * L ^ C) ^ 2 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) *
        (1 + Real.log (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ)) ^ 3)) ≤
      13824 * (Hm * Hn) ^ 2 * L ^ (4 * C + 4) := by
  have hL0 : 0 < L := by linarith only [hL]
  have hN := N4_le Hm Hn hHm hHn
  obtain ⟨hl0, hl⟩ := logN4_le Hm Hn L hHm hHn hL hlog
  set N : ℝ := ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) with hNdef
  set lN := 1 + Real.log N with hlN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hX0 : 0 ≤ Hm * Hn := by positivity
  rw [rpow_C_sq L C hL0]
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hA : Real.pi * (2 * π * (Hm * Hn)) + 2 * Real.pi * N * lN ≤ 128 * (Hm * Hn) * L := by
    have h1 : Real.pi * (2 * π * (Hm * Hn)) ≤ 32 * (Hm * Hn) := by
      have hpp := mul_le_mul hpi hpi Real.pi_pos.le (by norm_num)
      have : Real.pi * (2 * π) ≤ 32 := by linarith only [hpp]
      have h' := mul_le_mul_of_nonneg_right this hX0
      linarith only [h']
    have h2 : 2 * Real.pi * N * lN ≤ 2 * 4 * (4 * (Hm * Hn)) * (3 * L) := by
      gcongr
    have h3 : 32 * (Hm * Hn) ≤ 32 * (Hm * Hn) * L := by
      have h' := mul_le_mul_of_nonneg_left hL (show 0 ≤ 32 * (Hm * Hn) by positivity)
      linarith only [h']
    linarith only [h1, h2, h3]
  have hB : N * lN ^ 3 ≤ (4 * (Hm * Hn)) * (3 * L) ^ 3 := by gcongr
  have hLC : 0 ≤ L ^ (4 * C) := by positivity
  calc (Real.pi * (2 * π * (Hm * Hn)) + 2 * Real.pi * N * lN) * (L ^ (4 * C) * (N * lN ^ 3))
      ≤ (128 * (Hm * Hn) * L) * (L ^ (4 * C) * ((4 * (Hm * Hn)) * (3 * L) ^ 3)) := by
        gcongr
    _ = 13824 * (Hm * Hn) ^ 2 * (L ^ (4 * C) * L ^ (4 : ℕ)) := by ring
    _ = 13824 * (Hm * Hn) ^ 2 * L ^ (4 * C + 4) := by
        rw [Real.rpow_add hL0]; norm_cast

lemma rpow_mul3 (L a b c : ℝ) (hL : 0 < L) : L ^ a * L ^ b * L ^ c = L ^ (a + b + c) := by
  rw [Real.rpow_add hL, Real.rpow_add hL]

lemma rpow_sq' (L a : ℝ) (hL : 0 < L) : (L ^ a) ^ 2 = L ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; push_cast; ring_nf

/-- The `U`-side, normalized (pure arithmetic in the polylog exponents). -/
lemma MU_norm (L X R Q I₀ nP W E tail : ℝ) (A' B₁ D₂ As A A₀ C Cp Lη : ℝ)
    (hL : 1 ≤ L) (hX : 0 < X) (hR : 0 ≤ R) (hI₀0 : 0 ≤ I₀)
    (hI₀ : I₀ ≤ 5400 * X ^ 2 * L ^ (B₁ + 4 * C + 3))
    (hQ : Q ≤ L ^ (-(2 * As)) * I₀ + 1800 * Cp ^ 2 * X ^ 2 * L ^ (2 * C + 1 - 2 * A))
    (hnP0 : 0 ≤ nP) (hnP : nP ≤ 2 * L ^ (0.2 + D₂ + A₀))
    (hW : W ^ 2 ≤ 4 * R ^ 2)
    (hE : E ^ 2 ≤ R ^ 2 * (1024 * (Lη + 13) ^ 2 * L ^ (2 * A₀ - 2 * D₂)))
    (htail : tail ≤ R ^ 2 * (10 ^ 6 * X ^ 2 * L ^ (4 * C + 3 - B₁)))
    (hB₁ : B₁ = A' + 4 * C + 3) (hD₂ : 2 * D₂ = A' + 2 * A₀ + B₁ + 4 * C + 3)
    (hAs : 2 * As = A' + 0.4 + 2 * D₂ + 2 * A₀ + B₁ + 4 * C + 3)
    (hA : 2 * A = A' + 0.4 + 2 * D₂ + 2 * A₀ + 2 * C + 1) :
    2 * nP * W ^ 2 * (nP * Q) + 2 * E ^ 2 * I₀ + tail ≤
      R ^ 2 * X ^ 2 * ((172800 + 57600 * Cp ^ 2 + 11059200 * (Lη + 13) ^ 2 + 10 ^ 6) *
        L ^ (-A')) := by
  have hL0 : 0 < L := by linarith
  have hQ0' : 0 ≤ L ^ (-(2 * As)) * I₀ + 1800 * Cp ^ 2 * X ^ 2 * L ^ (2 * C + 1 - 2 * A) := by
    positivity
  have hnP2 : nP ^ 2 ≤ 4 * L ^ (0.4 + 2 * D₂ + 2 * A₀) := by
    have := pow_le_pow_left₀ hnP0 hnP 2
    rw [mul_pow, rpow_sq' L _ hL0] at this
    calc nP ^ 2 ≤ 2 ^ 2 * L ^ (2 * (0.2 + D₂ + A₀)) := this
      _ = 4 * L ^ (0.4 + 2 * D₂ + 2 * A₀) := by norm_num; ring_nf
  -- term 1 + 2
  have hT12 : 2 * nP * W ^ 2 * (nP * Q) ≤ R ^ 2 * X ^ 2 *
      ((172800 + 57600 * Cp ^ 2) * L ^ (-A')) := by
    have hQ0 : 2 * nP * W ^ 2 * (nP * Q) = 2 * nP ^ 2 * W ^ 2 * Q := by ring
    rw [hQ0]
    by_cases hQs : Q ≤ 0
    · have h1 : 2 * nP ^ 2 * W ^ 2 * Q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hQs
      have h2 : 0 ≤ R ^ 2 * X ^ 2 * ((172800 + 57600 * Cp ^ 2) * L ^ (-A')) := by positivity
      linarith only [h1, h2]
    push_neg at hQs
    calc 2 * nP ^ 2 * W ^ 2 * Q
        ≤ 2 * (4 * L ^ (0.4 + 2 * D₂ + 2 * A₀)) * (4 * R ^ 2) *
          (L ^ (-(2 * As)) * (5400 * X ^ 2 * L ^ (B₁ + 4 * C + 3)) +
            1800 * Cp ^ 2 * X ^ 2 * L ^ (2 * C + 1 - 2 * A)) := by
          gcongr
          exact hQ.trans (by gcongr)
      _ = R ^ 2 * X ^ 2 * (172800 * (L ^ (0.4 + 2 * D₂ + 2 * A₀) * L ^ (-(2 * As)) *
            L ^ (B₁ + 4 * C + 3)) + 57600 * Cp ^ 2 * (L ^ (0.4 + 2 * D₂ + 2 * A₀) *
            L ^ (2 * C + 1 - 2 * A))) := by ring
      _ = R ^ 2 * X ^ 2 * ((172800 + 57600 * Cp ^ 2) * L ^ (-A')) := by
          rw [rpow_mul3 L _ _ _ hL0, ← Real.rpow_add hL0]
          have e1 : 0.4 + 2 * D₂ + 2 * A₀ + -(2 * As) + (B₁ + 4 * C + 3) = -A' := by
            linarith only [hB₁, hD₂, hAs, hA]
          have e2 : 0.4 + 2 * D₂ + 2 * A₀ + (2 * C + 1 - 2 * A) = -A' := by
            linarith only [hB₁, hD₂, hAs, hA]
          rw [e1, e2]; ring
  -- term 3
  have hT3 : 2 * E ^ 2 * I₀ ≤ R ^ 2 * X ^ 2 * ((11059200 * (Lη + 13) ^ 2) * L ^ (-A')) := by
    calc 2 * E ^ 2 * I₀
        ≤ 2 * (R ^ 2 * (1024 * (Lη + 13) ^ 2 * L ^ (2 * A₀ - 2 * D₂))) *
          (5400 * X ^ 2 * L ^ (B₁ + 4 * C + 3)) := by gcongr
      _ = R ^ 2 * X ^ 2 * (11059200 * (Lη + 13) ^ 2 * (L ^ (2 * A₀ - 2 * D₂) *
            L ^ (B₁ + 4 * C + 3))) := by ring
      _ = R ^ 2 * X ^ 2 * ((11059200 * (Lη + 13) ^ 2) * L ^ (-A')) := by
          rw [← Real.rpow_add hL0]
          have e : 2 * A₀ - 2 * D₂ + (B₁ + 4 * C + 3) = -A' := by
            linarith only [hB₁, hD₂, hAs, hA]
          rw [e]
  -- term 4
  have hT4 : tail ≤ R ^ 2 * X ^ 2 * (10 ^ 6 * L ^ (-A')) := by
    have e : 4 * C + 3 - B₁ = -A' := by linarith only [hB₁]
    rw [e] at htail; linarith only [htail]
  calc 2 * nP * W ^ 2 * (nP * Q) + 2 * E ^ 2 * I₀ + tail
      ≤ R ^ 2 * X ^ 2 * ((172800 + 57600 * Cp ^ 2) * L ^ (-A')) +
        R ^ 2 * X ^ 2 * ((11059200 * (Lη + 13) ^ 2) * L ^ (-A')) +
        R ^ 2 * X ^ 2 * (10 ^ 6 * L ^ (-A')) := by linarith only [hT12, hT3, hT4]
    _ = _ := by ring

/-- The arc bound, normalized (pure arithmetic). -/
lemma Gth_norm (G sqN Ksep lam k MU MV L X Y R cU A' A₀ C D : ℝ) (hL : 1 ≤ L) (hX : 0 < X)
    (hsq : 0 ≤ sqN) (hK : 0 ≤ Ksep) (hk0 : 0 ≤ k) (hcU : 0 ≤ cU)
    (hsqR : sqN * R ^ 2 = 16 * Y ^ 2)
    (hlam : |lam| ≤ 2 * L ^ A₀) (hk : k ≤ L ^ A₀) (hA₀ : 0 < A₀)
    (hMU : MU ≤ R ^ 2 * X ^ 2 * (cU * L ^ (-A')))
    (hMV : MV ≤ R ^ 2 * (13824 * X ^ 2 * L ^ (4 * C + 4)))
    (hA' : A' = 2 * D + 26 * A₀ + 4 * C + 4)
    (hG : G ≤ sqN * (Ksep * (1 + |lam|) ^ 4 * (L ^ ((A' + 4 * C + 4) / 2) * (k ^ 6 * MU) +
      k ^ 6 * MV / L ^ ((A' + 4 * C + 4) / 2)) / (4 * X))) :
    G ≤ 324 * Ksep * (cU + 13824) * (X * Y ^ 2 * L ^ (-(D + 3 * A₀))) := by
  have hL0 : 0 < L := by linarith
  set ε := L ^ ((A' + 4 * C + 4) / 2) with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hL0 _
  have hLA : 1 ≤ L ^ A₀ := Real.one_le_rpow hL hA₀.le
  have hlam4 : (1 + |lam|) ^ 4 ≤ 81 * L ^ (4 * A₀) := by
    have : 1 + |lam| ≤ 3 * L ^ A₀ := by linarith only [hlam, hLA]
    calc (1 + |lam|) ^ 4 ≤ (3 * L ^ A₀) ^ 4 := by gcongr
      _ = 81 * (L ^ A₀) ^ 4 := by ring
      _ = 81 * L ^ (4 * A₀) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; push_cast; ring_nf
  have hk6 : k ^ 6 ≤ L ^ (6 * A₀) := by
    calc k ^ 6 ≤ (L ^ A₀) ^ 6 := by gcongr
      _ = L ^ (6 * A₀) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; push_cast; ring_nf
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
  have hMU0 : MU ≤ R ^ 2 * X ^ 2 * cU * L ^ (-A') := by linarith only [hMU]
  have hbr : ε * (k ^ 6 * MU) + k ^ 6 * MV / ε ≤
      L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * (cU + 13824) * L ^ ((4 * C + 4 - A') / 2)) := by
    have h1 : ε * (k ^ 6 * MU) ≤ ε * (L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * (cU * L ^ (-A')))) := by
      by_cases hMUs : MU ≤ 0
      · have h1 : ε * (k ^ 6 * MU) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hε0.le (mul_nonpos_of_nonneg_of_nonpos (by positivity) hMUs)
        have h2 : 0 ≤ ε * (L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * (cU * L ^ (-A')))) := by positivity
        linarith only [h1, h2]
      · push_neg at hMUs
        gcongr
    have h2 : k ^ 6 * MV / ε ≤ L ^ (6 * A₀) * (R ^ 2 * (13824 * X ^ 2 * L ^ (4 * C + 4))) / ε := by
      by_cases hMVs : MV ≤ 0
      · have : k ^ 6 * MV / ε ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ hε0.le
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hMVs
        have h3 : 0 ≤ L ^ (6 * A₀) * (R ^ 2 * (13824 * X ^ 2 * L ^ (4 * C + 4))) / ε := by positivity
        linarith only [this, h3]
      · push_neg at hMVs
        gcongr
    have e1 : ε * (L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * (cU * L ^ (-A')))) =
        L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * cU * L ^ ((4 * C + 4 - A') / 2)) := by
      rw [hε]
      have : L ^ ((A' + 4 * C + 4) / 2) * L ^ (-A') = L ^ ((4 * C + 4 - A') / 2) := by
        rw [← Real.rpow_add hL0]; congr 1; ring
      calc L ^ ((A' + 4 * C + 4) / 2) * (L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * (cU * L ^ (-A'))))
          = L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * cU * (L ^ ((A' + 4 * C + 4) / 2) * L ^ (-A'))) := by
            ring
        _ = _ := by rw [this]
    have e2 : L ^ (6 * A₀) * (R ^ 2 * (13824 * X ^ 2 * L ^ (4 * C + 4))) / ε =
        L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * 13824 * L ^ ((4 * C + 4 - A') / 2)) := by
      rw [hε]
      have : L ^ (4 * C + 4) / L ^ ((A' + 4 * C + 4) / 2) = L ^ ((4 * C + 4 - A') / 2) := by
        rw [← Real.rpow_sub hL0]; congr 1; ring
      calc L ^ (6 * A₀) * (R ^ 2 * (13824 * X ^ 2 * L ^ (4 * C + 4))) / L ^ ((A' + 4 * C + 4) / 2)
          = L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * 13824 *
              (L ^ (4 * C + 4) / L ^ ((A' + 4 * C + 4) / 2))) := by ring
        _ = _ := by rw [this]
    rw [e1] at h1; rw [e2] at h2
    linarith only [h1, h2]
  have hfin : sqN * (Ksep * (1 + |lam|) ^ 4 * (ε * (k ^ 6 * MU) + k ^ 6 * MV / ε) / (4 * X)) ≤
      sqN * (Ksep * (81 * L ^ (4 * A₀)) * (L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * (cU + 13824) *
        L ^ ((4 * C + 4 - A') / 2))) / (4 * X)) := by
    have hbr0 : 0 ≤ ε * (k ^ 6 * MU) + k ^ 6 * MV / ε ∨ ε * (k ^ 6 * MU) + k ^ 6 * MV / ε < 0 :=
      le_or_gt 0 _
    rcases hbr0 with h | h
    · gcongr
    · have h1 : sqN * (Ksep * (1 + |lam|) ^ 4 * (ε * (k ^ 6 * MU) + k ^ 6 * MV / ε) / (4 * X)) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos hsq
        apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
        apply mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
      have h2 : 0 ≤ sqN * (Ksep * (81 * L ^ (4 * A₀)) * (L ^ (6 * A₀) * (R ^ 2 * X ^ 2 *
          (cU + 13824) * L ^ ((4 * C + 4 - A') / 2))) / (4 * X)) := by positivity
      linarith only [h1, h2]
  refine hG.trans (hfin.trans (le_of_eq ?_))
  have eL : L ^ (4 * A₀) * L ^ (6 * A₀) * L ^ ((4 * C + 4 - A') / 2) = L ^ (-(D + 3 * A₀)) := by
    rw [rpow_mul3 L _ _ _ hL0]; congr 1; rw [hA']; ring
  have hX' : X ≠ 0 := hX.ne'
  calc sqN * (Ksep * (81 * L ^ (4 * A₀)) * (L ^ (6 * A₀) * (R ^ 2 * X ^ 2 * (cU + 13824) *
        L ^ ((4 * C + 4 - A') / 2))) / (4 * X))
      = (sqN * R ^ 2) * (81 * Ksep * (cU + 13824)) * X *
          (L ^ (4 * A₀) * L ^ (6 * A₀) * L ^ ((4 * C + 4 - A') / 2)) / 4 := by
        field_simp
    _ = 324 * Ksep * (cU + 13824) * (X * Y ^ 2 * L ^ (-(D + 3 * A₀))) := by
        rw [hsqR, eL]; ring

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: the `U`-side bound for one residue class

Combines `MU_split`, `bound_521`, `lemma53` (as a hypothesis instance), `MN_int_le` and
`MU_norm`: `∫ ω_X |𝔅𝔐𝔑|² ≤ (4Y∏V)² X² c_U L^{-A'}`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset MeasureTheory

noncomputable section

lemma Rpoly_eq_Fset (Hn : ℝ) (hHn : 0 ≤ Hn) (β : ℕ → ℂ)
    (hβ : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn) (k : ℕ) (ρ : ZMod k) (τ : ℝ) :
    Rpoly Hn β k ρ τ = ∑ n ∈ Fset Hn, (if (n : ZMod k) = ρ then β n else 0) * (n : ℂ) ^ (I * τ) := by
  unfold Rpoly Fset
  rw [Finset.sum_filter_of_ne]
  · refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  · intro n _ hne
    by_contra hlt
    apply hne
    have hb : β n = 0 := by
      by_contra hb; exact hlt (hβ n hb).1
    simp [hb]

lemma Rpoly_eq_Fset' (Hn : ℝ) (hHn : 0 ≤ Hn) (β : ℕ → ℂ)
    (hβ : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn) (k : ℕ) (ρ : ZMod k) :
    Rpoly Hn β k ρ = fun τ : ℝ =>
      ∑ n ∈ Fset Hn, (if (n : ZMod k) = ρ then β n else 0) * (n : ℂ) ^ (I * τ) := by
  funext τ; exact Rpoly_eq_Fset Hn hHn β hβ k ρ τ


lemma Pj_bounds (x : ℝ) {K' : ℕ} (a : Fin (K' + 1) → ℝ) (ha : 0.1 < a 0 ∧ a 0 < 0.2)
    (δs : ℝ) (hδ0 : 0 < δs) (hL1 : 1 ≤ Real.log x) (j : ℕ) (hj : j ∈ range (Jn x a δs)) :
    2 ≤ Pj x a δs j ∧ Real.log x ^ (0.1 : ℝ) ≤ Real.log (Pj x a δs j) ∧
      Real.log (Pj x a δs j) ≤ 3 * Real.log x ^ (0.2 : ℝ) := by
  have h1 : j ≤ ⌊Real.log x ^ a 0 / δs⌋₊ := by
    unfold Jn at hj; rw [mem_range] at hj; omega
  have hlogPj : Real.log (Pj x a δs j) = Real.log x ^ a 0 + j * δs := by
    unfold Pj Plo
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  have hjb : (j : ℝ) * δs ≤ Real.log x ^ a 0 := by
    have h2 : (j : ℝ) ≤ Real.log x ^ a 0 / δs :=
      (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
    rwa [le_div_iff₀ hδ0] at h2
  have hj0 : 0 ≤ (j : ℝ) * δs := by positivity
  have h01 : Real.log x ^ (0.1 : ℝ) ≤ Real.log x ^ a 0 :=
    Real.rpow_le_rpow_of_exponent_le hL1 ha.1.le
  have h02 : Real.log x ^ a 0 ≤ Real.log x ^ (0.2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 ha.2.le
  have h1' : 1 ≤ Real.log x ^ (0.1 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · have : Real.exp 1 ≤ Pj x a δs j := by
      rw [← Real.exp_log (show 0 < Pj x a δs j by unfold Pj Plo; positivity)]
      apply Real.exp_le_exp.mpr
      rw [hlogPj]; linarith
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
    linarith
  · rw [hlogPj]; linarith
  · rw [hlogPj]; linarith

lemma nP_le (x : ℝ) {K' : ℕ} (a : Fin (K' + 1) → ℝ) (ha : 0.1 < a 0 ∧ a 0 < 0.2)
    (D₂ A₀ : ℝ) (hD₂ : 0 ≤ D₂) (hA₀ : 0 ≤ A₀) (hL1 : 1 ≤ Real.log x) (k : ℕ)
    (hk : (k : ℝ) ≤ Real.log x ^ A₀) :
    ((Jn x a (Real.log x ^ (-D₂)) * k : ℕ) : ℝ) ≤ 2 * Real.log x ^ (0.2 + D₂ + A₀) := by
  have hL0 : 0 < Real.log x := by linarith
  have hδ : 0 < Real.log x ^ (-D₂) := Real.rpow_pos_of_pos hL0 _
  have hJ : (Jn x a (Real.log x ^ (-D₂)) : ℝ) ≤ 2 * Real.log x ^ (0.2 + D₂) := by
    unfold Jn
    push_cast
    have h1 : (⌊Real.log x ^ a 0 / Real.log x ^ (-D₂)⌋₊ : ℝ) ≤
        Real.log x ^ a 0 / Real.log x ^ (-D₂) := Nat.floor_le (by positivity)
    have h2 : Real.log x ^ a 0 / Real.log x ^ (-D₂) = Real.log x ^ (a 0 + D₂) := by
      rw [← Real.rpow_sub hL0]; ring_nf
    have h3 : Real.log x ^ (a 0 + D₂) ≤ Real.log x ^ (0.2 + D₂) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [ha.2])
    have h4 : 1 ≤ Real.log x ^ (0.2 + D₂) := Real.one_le_rpow hL1 (by linarith)
    linarith
  push_cast
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (Jn x a (Real.log x ^ (-D₂)) : ℝ) * k ≤ (2 * Real.log x ^ (0.2 + D₂)) * Real.log x ^ A₀ := by
        gcongr
    _ = 2 * Real.log x ^ (0.2 + D₂ + A₀) := by rw [mul_assoc, ← Real.rpow_add hL0]

lemma W_bound (Y PV PV' : ℝ) (hY : 0 ≤ Y) (hPV' : 0 ≤ PV') (h : PV' ≤ 2 * PV) :
    (4 * Y * PV') ^ 2 ≤ 4 * (4 * Y * PV) ^ 2 := by
  have h1 : 4 * Y * PV' ≤ 2 * (4 * Y * PV) := by
    have := mul_le_mul_of_nonneg_left h hY; linarith only [this]
  have h0 : 0 ≤ 4 * Y * PV' := by positivity
  calc (4 * Y * PV') ^ 2 ≤ (2 * (4 * Y * PV)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 4 * (4 * Y * PV) ^ 2 := by ring

lemma E_bound (L δs lam Lη A₀ D₂ Y PV : ℝ) (hL1 : 1 ≤ L) (hA₀ : 0 < A₀) (hLη0 : 0 ≤ Lη)
    (hδs : δs = L ^ (-D₂)) (hlam : |lam| ≤ 2 * L ^ A₀) :
    (16 * δs * (Lη + 2 * π * |lam|) * (8 * Y * PV)) ^ 2 ≤
      (4 * Y * PV) ^ 2 * (1024 * (Lη + 13) ^ 2 * L ^ (2 * A₀ - 2 * D₂)) := by
  have hL0 : 0 < L := by linarith only [hL1]
  have hLA : 1 ≤ L ^ A₀ := Real.one_le_rpow hL1 hA₀.le
  have hLip : Lη + 2 * π * |lam| ≤ (Lη + 13) * L ^ A₀ := by
    have h1 : 2 * π * |lam| ≤ 2 * π * (2 * L ^ A₀) := by gcongr
    have h2 : 2 * π * (2 * L ^ A₀) ≤ 13 * L ^ A₀ := by
      have := Real.pi_lt_d2; nlinarith only [this, hLA]
    have h3 : Lη ≤ Lη * L ^ A₀ := by nlinarith only [hLη0, hLA]
    linarith only [h1, h2, h3]
  have hlip0 : 0 ≤ Lη + 2 * π * |lam| := by positivity
  have e2 : δs ^ 2 * L ^ (2 * A₀) = L ^ (2 * A₀ - 2 * D₂) := by
    rw [hδs, rpow_sq' L _ hL0, ← Real.rpow_add hL0]; ring_nf
  have h1 : (Lη + 2 * π * |lam|) ^ 2 ≤ (Lη + 13) ^ 2 * L ^ (2 * A₀) := by
    rw [← rpow_sq' L _ hL0, ← mul_pow]
    exact pow_le_pow_left₀ hlip0 hLip 2
  calc (16 * δs * (Lη + 2 * π * |lam|) * (8 * Y * PV)) ^ 2 =
        (4 * Y * PV) ^ 2 * (1024 * δs ^ 2 * (Lη + 2 * π * |lam|) ^ 2) := by ring
    _ ≤ (4 * Y * PV) ^ 2 * (1024 * δs ^ 2 * ((Lη + 13) ^ 2 * L ^ (2 * A₀))) := by gcongr
    _ = (4 * Y * PV) ^ 2 * (1024 * (Lη + 13) ^ 2 * (δs ^ 2 * L ^ (2 * A₀))) := by ring
    _ = _ := by rw [e2]

lemma tail_bound (L X R B₁ C N4 lN : ℝ) (hL1 : 1 ≤ L) (hX0 : 0 < X) (hB₁1 : 1 ≤ B₁)
    (hN40 : 0 ≤ N4) (hN4 : N4 ≤ 4 * X) (hl0 : 0 ≤ lN) (hl : lN ≤ 3 * L)
    (hcoef : (L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3) ≤ 108 * X * L ^ (4 * C + 3)) :
    2 * (2 * π * X / (X * L ^ B₁)) ^ 2 * (R ^ 2 *
      ((Real.pi * (X * L ^ B₁) + 2 * Real.pi * N4 * lN) * ((L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3)))) ≤
      R ^ 2 * (10 ^ 6 * X ^ 2 * L ^ (4 * C + 3 - B₁)) := by
  have hL0 : 0 < L := by linarith only [hL1]
  have hLB0 : 0 < L ^ B₁ := Real.rpow_pos_of_pos hL0 _
  have h1 : (2 * π * X / (X * L ^ B₁)) ^ 2 = 4 * π ^ 2 * (L ^ B₁)⁻¹ ^ 2 := by
    field_simp; norm_num
  have hpi : π ^ 2 ≤ 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
  have hLLB : L ≤ L ^ B₁ := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ B₁ := Real.rpow_le_rpow_of_exponent_le hL1 hB₁1
  have h2 : Real.pi * (X * L ^ B₁) + 2 * Real.pi * N4 * lN ≤ 100 * (X * L ^ B₁) := by
    have h3 : 2 * Real.pi * N4 * lN ≤ 2 * 4 * (4 * X) * (3 * L) := by
      have := Real.pi_le_four
      gcongr
    have h4 : Real.pi * (X * L ^ B₁) ≤ 4 * (X * L ^ B₁) := by
      gcongr; exact Real.pi_le_four
    have hXL : X * L ≤ X * L ^ B₁ := mul_le_mul_of_nonneg_left hLLB hX0.le
    have e : 2 * 4 * (4 * X) * (3 * L) = 96 * (X * L) := by ring
    linarith only [h3, h4, hXL, e]
  have h0 : 0 ≤ Real.pi * (X * L ^ B₁) + 2 * Real.pi * N4 * lN := by positivity
  have hc0 : 0 ≤ (L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3) := by positivity
  have e3 : (L ^ B₁)⁻¹ ^ 2 * L ^ B₁ * L ^ (4 * C + 3) = L ^ (4 * C + 3 - B₁) := by
    rw [inv_pow, rpow_sq' L _ hL0, ← Real.rpow_neg hL0.le, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0]; ring_nf
  calc 2 * (2 * π * X / (X * L ^ B₁)) ^ 2 * (R ^ 2 *
        ((Real.pi * (X * L ^ B₁) + 2 * Real.pi * N4 * lN) * ((L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3))))
      ≤ 2 * (4 * π ^ 2 * (L ^ B₁)⁻¹ ^ 2) * (R ^ 2 *
        ((100 * (X * L ^ B₁)) * (108 * X * L ^ (4 * C + 3)))) := by
        rw [h1]; gcongr
    _ = R ^ 2 * (86400 * π ^ 2 * X ^ 2 * ((L ^ B₁)⁻¹ ^ 2 * L ^ B₁ * L ^ (4 * C + 3))) := by ring
    _ ≤ R ^ 2 * (10 ^ 6 * X ^ 2 * L ^ (4 * C + 3 - B₁)) := by
        rw [e3]
        have : 0 ≤ X ^ 2 * L ^ (4 * C + 3 - B₁) := by positivity
        have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
        gcongr
        nlinarith only [hpi]

lemma I0_arith (L X B₁ C N4 lN T₀ : ℝ) (hL1 : 1 ≤ L) (hX0 : 0 < X) (hB₁1 : 1 ≤ B₁)
    (hT₀ : T₀ = X * L ^ B₁) (hN40 : 0 ≤ N4) (hN4 : N4 ≤ 4 * X) (hl0 : 0 ≤ lN) (hl : lN ≤ 3 * L)
    (hcoef : (L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3) ≤ 108 * X * L ^ (4 * C + 3)) :
    (T₀ - -T₀ + 4 * N4 * lN) * ((L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3)) ≤
      5400 * X ^ 2 * L ^ (B₁ + 4 * C + 3) := by
  have hL0 : 0 < L := by linarith
  have h1 : T₀ - -T₀ + 4 * N4 * lN ≤ 50 * X * L ^ B₁ := by
    have h4 : 4 * N4 * lN ≤ 4 * (4 * X) * (3 * L) := by gcongr
    have hLLB : L ≤ L ^ B₁ := by
      calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
        _ ≤ L ^ B₁ := Real.rpow_le_rpow_of_exponent_le hL1 hB₁1
    have hXL : X * L ≤ X * L ^ B₁ := mul_le_mul_of_nonneg_left hLLB hX0.le
    have e : T₀ - -T₀ = 2 * (X * L ^ B₁) := by rw [hT₀]; ring
    have e2 : 4 * (4 * X) * (3 * L) = 48 * (X * L) := by ring
    rw [e]; linarith
  have h0 : 0 ≤ T₀ - -T₀ + 4 * N4 * lN := by
    have hT0 : 0 ≤ T₀ := by rw [hT₀]; positivity
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hN40) hl0
    linarith
  have hc0 : 0 ≤ (L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3) := by positivity
  calc (T₀ - -T₀ + 4 * N4 * lN) * ((L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3))
      ≤ (50 * X * L ^ B₁) * (108 * X * L ^ (4 * C + 3)) := by gcongr
    _ = 5400 * X ^ 2 * (L ^ B₁ * L ^ (4 * C + 3)) := by ring
    _ = 5400 * X ^ 2 * L ^ (B₁ + 4 * C + 3) := by rw [← Real.rpow_add hL0]; ring_nf

lemma coef_bound (L X C N4 lN : ℝ) (hL1 : 1 ≤ L) (hX : 0 ≤ X) (hN40 : 0 ≤ N4) (hN4 : N4 ≤ 4 * X)
    (hl0 : 0 ≤ lN) (hl : lN ≤ 3 * L) :
    (L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3) ≤ 108 * X * L ^ (4 * C + 3) := by
  have hL0 : 0 < L := by linarith
  rw [rpow_C_sq L C hL0]
  have : N4 * lN ^ 3 ≤ (4 * X) * (3 * L) ^ 3 := by gcongr
  have hLC : 0 ≤ L ^ (4 * C) := by positivity
  calc L ^ (4 * C) * (N4 * lN ^ 3) ≤ L ^ (4 * C) * ((4 * X) * (3 * L) ^ 3) := by gcongr
    _ = 108 * X * (L ^ (4 * C) * L ^ (3 : ℕ)) := by ring
    _ = 108 * X * L ^ (4 * C + 3) := by rw [Real.rpow_add hL0]; norm_cast

lemma Q_arith (L X Hm Hn Cp A As C I₀ : ℝ) (hL0 : 0 < L) (hX : X = Hm * Hn) :
    (L ^ (-As)) ^ 2 * I₀ + 4 * (Hm * Cp * L ^ (-A)) ^ 2 * (450 * Hn ^ 2 * L ^ (2 * C + 1)) =
      L ^ (-(2 * As)) * I₀ + 1800 * Cp ^ 2 * X ^ 2 * L ^ (2 * C + 1 - 2 * A) := by
  have e1 : (L ^ (-As)) ^ 2 = L ^ (-(2 * As)) := by rw [rpow_sq' L _ hL0]; ring_nf
  have e2 : (L ^ (-A)) ^ 2 * L ^ (2 * C + 1) = L ^ (2 * C + 1 - 2 * A) := by
    rw [rpow_sq' L _ hL0, ← Real.rpow_add hL0]; ring_nf
  rw [e1, hX, ← e2]; ring

/-- **The `U`-side bound for one residue class.** -/
theorem MU_rho (x : ℝ) {K' : ℕ} (a : Fin (K' + 1) → ℝ) (ha : 0.1 < a 0 ∧ a 0 < 0.2)
    (Y lam : ℝ) (hY : 1 ≤ Y) (k : ℕ) [NeZero k] (ρ : ZMod k × ZMod k × ZMod k)
    (Hm Hn : ℝ) (hHm : 0 < Hm) (hHn : 0 < Hn) (α β : ℕ → ℂ) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (C : ℝ) (hαB : ∀ m, ‖α m‖ ≤ Real.log x ^ C) (hβB : ∀ n, ‖β n‖ ≤ Real.log x ^ C)
    (hβsupp : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn)
    (hV : ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i)) (hL1 : 1 ≤ Real.log x)
    (A₀ A' B₁ D₂ As A Cp Lη : ℝ) (hA₀ : 0 < A₀) (hCp : 0 ≤ Cp) (hLη0 : 0 ≤ Lη)
    (hLη : ∀ y y' : ℝ, |dyadicBump y - dyadicBump y'| ≤ Lη * |y - y'|)
    (hB₁ : B₁ = A' + 4 * C + 3) (hB₁1 : 1 ≤ B₁) (hD₂0 : 0 < D₂)
    (hD₂ : 2 * D₂ = A' + 2 * A₀ + B₁ + 4 * C + 3)
    (hAs : 2 * As = A' + 0.4 + 2 * D₂ + 2 * A₀ + B₁ + 4 * C + 3)
    (hA : 2 * A = A' + 0.4 + 2 * D₂ + 2 * A₀ + 2 * C + 1)
    (hlam : |lam| ≤ 2 * Real.log x ^ A₀) (hk : (k : ℝ) ≤ Real.log x ^ A₀)
    (hδs : Real.log x ^ (-D₂) ≤ 1 / 2)
    (hlog4X : Real.log (4 * (Hm * Hn)) ≤ 2 * Real.log x)
    (hT : 2 * π * (Hm * Hn) ≤ Hm * Hn * Real.log x ^ B₁)
    (hTx : Hm * Hn * Real.log x ^ B₁ ≤ x ^ 3)
    (hM : ∀ τ : ℝ, |τ| ≤ Hm * Hn * Real.log x ^ B₁ →
      ‖Rpoly Hm α k ρ.2.1 τ‖ ≤ Hm * Cp * Real.log x ^ (-A))
    (h53 : ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ Real.log x ^ C) →
      ∀ P : ℝ, 2 ≤ P → Real.log x ^ (0.1 : ℝ) ≤ Real.log P →
      Real.log P ≤ 3 * Real.log x ^ (0.2 : ℝ) →
      ∀ 𝒮 : Finset ℕ, (∀ p ∈ 𝒮, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Z : ℝ, 0 ≤ Z → Z ≤ x ^ 3 →
      ∀ M : ℝ → ℂ, Continuous M → ∀ εM : ℝ, (∀ τ : ℝ, |τ| ≤ Z → ‖M τ‖ ≤ εM) →
      ∫ τ in (-Z)..Z, ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 *
          ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * τ)‖ ^ 2 ≤
        (Real.log x ^ (-As)) ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 *
          ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * τ)‖ ^ 2) +
        4 * εM ^ 2 * (450 * Hn ^ 2 * Real.log x ^ (2 * C + 1))) :
    ∫ τ, ωX (Hm * Hn) τ *
        ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 ≤
      (4 * Y * ∏ i, groupReciprocalSum x (a i)) ^ 2 * (Hm * Hn) ^ 2 *
        ((172800 + 57600 * Cp ^ 2 + 11059200 * (Lη + 13) ^ 2 + 10 ^ 6) *
          Real.log x ^ (-A')) := by
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith only [hL1]
  set X := Hm * Hn with hX
  have hX0 : 0 < X := mul_pos hHm hHn
  set T₀ := X * L ^ B₁ with hT₀
  have hT₀0 : 0 ≤ T₀ := (mul_pos hX0 (Real.rpow_pos_of_pos hL0 _)).le
  set δs := L ^ (-D₂) with hδs'
  have hδ0 : 0 < δs := Real.rpow_pos_of_pos hL0 _
  have hY0 : 0 < Y := by linarith only [hY]
  -- the split
  have hsplit := MU_split x a Y lam hY0 k ρ Hm Hn hHm.le hHn.le α β hα0 hβ0 (L ^ C) (L ^ C)
    hαB hβB X T₀ hX0 hT
  set M := Rpoly Hm α k ρ.2.1 with hMdef
  set N := Rpoly Hn β k ρ.2.2 with hNdef
  have hMc : Continuous M := Rpoly_continuous Hm α hα0 k ρ.2.1
  have hNc : Continuous N := Rpoly_continuous Hn β hβ0 k ρ.2.2
  set c3 : ℕ → ℂ := fun n => if (n : ZMod k) = ρ.2.2 then β n else 0 with hc3
  have hc3B : ∀ n, ‖c3 n‖ ≤ L ^ C := by
    intro n; rw [hc3]; simp only
    split_ifs
    · exact hβB n
    · simp only [norm_zero]; exact (Real.rpow_pos_of_pos hL0 _).le
  have hNeq : N = fun τ : ℝ => ∑ n ∈ Fset Hn, c3 n * (n : ℂ) ^ (I * τ) :=
    Rpoly_eq_Fset' Hn hHn.le β hβsupp k ρ.2.2
  set εM := Hm * Cp * L ^ (-A) with hεM
  set I₀ := ∫ τ in (-T₀)..T₀, ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 with hI₀
  set Q := (L ^ (-As)) ^ 2 * I₀ + 4 * εM ^ 2 * (450 * Hn ^ 2 * L ^ (2 * C + 1)) with hQdef
  have hQ : ∀ j ∈ range (Jn x a δs), ∀ u : ZMod k, ∫ τ in (-T₀)..T₀,
      ‖Pf (Spiece x a δs k j u) (Pj x a δs j) τ‖ ^ 2 * ‖M τ‖ ^ 2 * ‖N τ‖ ^ 2 ≤ Q := by
    intro j hj u
    obtain ⟨hP2, hPl, hPu⟩ := Pj_bounds x a ha δs hδ0 hL1 j hj
    have := h53 c3 hc3B (Pj x a δs j) hP2 hPl hPu (Spiece x a δs k j u)
      (Spiece_mem x a δs k hδ0 hδs j u) T₀ hT₀0 hTx M hMc εM hM
    have hNτ : ∀ τ : ℝ, ∑ n ∈ Fset Hn, c3 n * (n : ℂ) ^ (I * τ) = N τ := fun τ =>
      (congrFun hNeq τ).symm
    simp only [hNτ] at this
    exact this
  have hB521 := bound_521 x a Y lam δs k ρ.1 hδ0 hδs hY0 Lη hLη0 hLη M N hMc hNc T₀ hT₀0 Q hQ
  -- the mean value of `MN`
  have hMN := MN_int_le Hm Hn hHm.le hHn.le α β hα0 hβ0 (L ^ C) (L ^ C) hαB hβB k ρ.2.1 ρ.2.2
    (-T₀) T₀ (by linarith only [hT₀0])
  have hN4 := N4_le Hm Hn hHm.le hHn.le
  obtain ⟨hl0, hl⟩ := logN4_le Hm Hn L hHm.le hHn.le hL1 hlog4X
  set N4 : ℝ := ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) with hN4def
  set lN := 1 + Real.log N4 with hlN
  have hN40 : 0 ≤ N4 := Nat.cast_nonneg _
  have hcoef := coef_bound L X C N4 lN hL1 hX0.le hN40 hN4 hl0 hl
  have hI₀b : I₀ ≤ 5400 * X ^ 2 * L ^ (B₁ + 4 * C + 3) := by
    have e : I₀ = ∫ τ in (-T₀)..T₀, ‖Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 := by
      rw [hI₀]; congr 1; funext τ; rw [norm_mul, mul_pow]
    rw [e]
    exact hMN.trans (I0_arith L X B₁ C N4 lN T₀ hL1 hX0 hB₁1 rfl hN40 hN4 hl0 hl hcoef)
  have hI₀0 : 0 ≤ I₀ := intervalIntegral.integral_nonneg (by linarith only [hT₀0])
    (fun τ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  -- the products of group reciprocal sums
  have hPVeq0 : (∏ i, groupReciprocalSum x (a i)) =
      groupReciprocalSum x (a 0) * ∏ i : Fin K', groupReciprocalSum x (a i.succ) :=
    Fin.prod_univ_succ _
  set PV := ∏ i, groupReciprocalSum x (a i) with hPV
  set PV' := ∏ i : Fin K', groupReciprocalSum x (a i.succ) with hPV'
  have hV0 : ∀ i, 0 < groupReciprocalSum x (a i) := fun i => by linarith only [hV i]
  have hPV'0 : 0 ≤ PV' := Finset.prod_nonneg fun i _ => (hV0 _).le
  have hPVeq : PV = groupReciprocalSum x (a 0) * PV' := hPVeq0
  have hPV'le : PV' ≤ 2 * PV := by
    have h1 : (1 / 2) * PV' ≤ groupReciprocalSum x (a 0) * PV' :=
      mul_le_mul_of_nonneg_right (hV 0) hPV'0
    linarith only [h1, hPVeq]
  set R := 4 * Y * PV with hR
  have hR0 : 0 ≤ R := by
    rw [hR]; exact mul_nonneg (by linarith only [hY]) (Finset.prod_nonneg fun i _ => (hV0 i).le)
  have hW := W_bound Y PV PV' (by linarith only [hY]) hPV'0 hPV'le
  have hE := E_bound L δs lam Lη A₀ D₂ Y PV hL1 hA₀ hLη0 rfl hlam
  have htail := tail_bound L X R B₁ C N4 lN hL1 hX0 hB₁1 hN40 hN4 hl0 hl hcoef
  have hnP := nP_le x a ha D₂ A₀ hD₂0.le hA₀.le hL1 k hk
  have hQb : Q ≤ L ^ (-(2 * As)) * I₀ + 1800 * Cp ^ 2 * X ^ 2 * L ^ (2 * C + 1 - 2 * A) :=
    le_of_eq (Q_arith L X Hm Hn Cp A As C I₀ hL0 hX)
  have hfinal := MU_norm L X R Q I₀ ((Jn x a δs * k : ℕ) : ℝ) (4 * Y * PV')
    (16 * δs * (Lη + 2 * π * |lam|) * (8 * Y * PV))
    (2 * (2 * π * X / T₀) ^ 2 * ((4 * Y * PV) ^ 2 *
      ((Real.pi * T₀ + 2 * Real.pi * N4 * lN) * ((L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3)))))
    A' B₁ D₂ As A A₀ C Cp Lη hL1 hX0 hR0 hI₀0 hI₀b hQb (Nat.cast_nonneg _) hnP hW hE htail
    hB₁ hD₂ hAs hA
  calc ∫ τ, ωX X τ * ‖Bpoly x a Y lam k ρ.1 τ * M τ * N τ‖ ^ 2
      ≤ (∫ τ in (-T₀)..T₀, ‖Bpoly x a Y lam k ρ.1 τ * M τ * N τ‖ ^ 2) +
        2 * (2 * π * X / T₀) ^ 2 * ((4 * Y * PV) ^ 2 *
          ((Real.pi * T₀ + 2 * Real.pi * N4 * lN) * ((L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3)))) := hsplit
    _ ≤ (2 * ((Jn x a δs * k : ℕ) : ℝ) * (4 * Y * PV') ^ 2 * (((Jn x a δs * k : ℕ) : ℝ) * Q) +
        2 * (16 * δs * (Lη + 2 * π * |lam|) * (8 * Y * PV)) ^ 2 * I₀) +
        2 * (2 * π * X / T₀) ^ 2 * ((4 * Y * PV) ^ 2 *
          ((Real.pi * T₀ + 2 * Real.pi * N4 * lN) * ((L ^ C * L ^ C) ^ 2 * (N4 * lN ^ 3)))) := by
        gcongr
    _ ≤ _ := by rw [← hR]; exact hfinal

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: asymptotic helper inequalities (in the variable `L = log x → ∞`)
-/

namespace ArtinPrimitiveRoots.L102M

open Real Filter Topology

lemma ev_const_mul_rpow_le (a b c : ℝ) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, c * L ^ a ≤ L ^ b := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop (max c 0)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with L hL hL0
  have e : L ^ b = L ^ (b - a) * L ^ a := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [e]
  have : 0 ≤ L ^ a := by positivity
  nlinarith [le_max_left c 0]

lemma log_le_rpow (ε : ℝ) (hε : 0 < ε) (L : ℝ) (hL : 0 ≤ L) :
    Real.log L ≤ L ^ ε / ε := Real.log_le_rpow_div hL hε

lemma ev_const_mul_rpow_log_le (a b c : ℝ) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, c * L ^ a * Real.log L ≤ L ^ b := by
  set ε := (b - a) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have h := ev_const_mul_rpow_le (a + ε) b (|c| / ε) (by rw [hε]; linarith)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with L hL hL1
  have hL0 : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  have hle := log_le_rpow ε hε0 L hL0.le
  calc c * L ^ a * Real.log L ≤ |c| * L ^ a * Real.log L := by
        have : 0 ≤ L ^ a * Real.log L := by positivity
        nlinarith [le_abs_self c]
    _ ≤ |c| * L ^ a * (L ^ ε / ε) := by gcongr
    _ = |c| / ε * L ^ (a + ε) := by
        rw [Real.rpow_add hL0]; ring
    _ ≤ L ^ b := hL

lemma ev_logpow_le_rpow (r ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, Real.log L ^ r ≤ L ^ ε := by
  have h := isLittleO_log_rpow_rpow_atTop r hε
  have hb := h.bound one_pos
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with L hL hL1
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hL1.le) _),
    Real.norm_of_nonneg (by positivity)] at hL
  exact hL

/-- Transfer from `L` to `x` via `L = log x`. -/
lemma ev_log {p : ℝ → Prop} (h : ∀ᶠ L : ℝ in atTop, p L) : ∀ᶠ x : ℝ in atTop, p (Real.log x) :=
  Real.tendsto_log_atTop.eventually h

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: from character sums to residue-class sums

If `c` is supported on integers coprime to `k` and every twisted sum
`∑_m c_m χ(m) m^{iτ}` has norm `≤ B`, then so does every residue-class sum `∑_{m ≡ ρ} c_m m^{iτ}`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex Finset

noncomputable section

theorem Rpoly_le_of_char (k : ℕ) [NeZero k] (H : ℝ) (c : ℕ → ℂ)
    (hcop : ∀ m, c m ≠ 0 → Nat.Coprime m k) (ρ : ZMod k) (τ B : ℝ)
    (hB : ∀ χ : DirichletCharacter ℂ k,
      ‖∑ m ∈ Finset.range (⌊2 * H⌋₊ + 1), c m * χ (m : ZMod k) * (m : ℂ) ^ (I * τ)‖ ≤ B) :
    ‖Rpoly H c k ρ τ‖ ≤ B := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 1)
  by_cases hu : IsUnit ρ
  · have htot : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos k)
    have hkey : ((k.totient : ℂ)) * Rpoly H c k ρ τ = ∑ χ : DirichletCharacter ℂ k, χ ρ⁻¹ *
        ∑ m ∈ Finset.range (⌊2 * H⌋₊ + 1), c m * χ (m : ZMod k) * (m : ℂ) ^ (I * τ) := by
      unfold Rpoly
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (m : ZMod k)
      have e : ∑ χ : DirichletCharacter ℂ k, χ ρ⁻¹ * (c m * χ (m : ZMod k) * (m : ℂ) ^ (I * τ)) =
          (∑ χ : DirichletCharacter ℂ k, χ ρ⁻¹ * χ (m : ZMod k)) * (c m * (m : ℂ) ^ (I * τ)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun χ _ => ?_; ring
      rw [e, h]
      by_cases hm : (m : ZMod k) = ρ
      · rw [if_pos hm, if_pos hm.symm]
      · rw [if_neg hm, if_neg (Ne.symm hm)]; ring
    have hcard : (Finset.univ : Finset (DirichletCharacter ℂ k)).card = k.totient := by
      rw [card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ k
    have hle : ‖((k.totient : ℂ)) * Rpoly H c k ρ τ‖ ≤ k.totient * B := by
      rw [hkey]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ χ : DirichletCharacter ℂ k, ‖χ ρ⁻¹ *
            ∑ m ∈ Finset.range (⌊2 * H⌋₊ + 1), c m * χ (m : ZMod k) * (m : ℂ) ^ (I * τ)‖
          ≤ ∑ _χ : DirichletCharacter ℂ k, B := by
            refine Finset.sum_le_sum fun χ _ => ?_
            rw [norm_mul]
            calc ‖χ ρ⁻¹‖ * ‖∑ m ∈ Finset.range (⌊2 * H⌋₊ + 1), c m * χ (m : ZMod k) *
                  (m : ℂ) ^ (I * τ)‖ ≤ 1 * B := by
                  gcongr
                  · exact DirichletCharacter.norm_le_one χ _
                  · exact hB χ
              _ = B := one_mul B
        _ = k.totient * B := by rw [sum_const, hcard, nsmul_eq_mul]
    rw [norm_mul, Complex.norm_natCast] at hle
    exact le_of_mul_le_mul_left hle htot
  · have hzero : Rpoly H c k ρ τ = 0 := by
      unfold Rpoly
      refine Finset.sum_eq_zero fun m _ => ?_
      split_ifs with hm
      · by_cases hc : c m = 0
        · rw [hc, zero_mul]
        · exfalso; apply hu
          rw [← hm]
          exact (ZMod.isUnit_iff_coprime m k).mpr (hcop m hc)
      · rfl
    rw [hzero, norm_zero]; exact hB0

/-- Rough integers are coprime to small moduli. -/
lemma coprime_of_rough {y : ℝ} {m k : ℕ} (hm : IsRough y m) (hk : 0 < k) (hky : (k : ℝ) ≤ y) :
    Nat.Coprime m k := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpk
  have h1 : y < p := hm.2 p (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.1.ne'⟩)
  have h2 : p ≤ k := Nat.le_of_dvd hk hpk
  have : (p : ℝ) ≤ k := by exact_mod_cast h2
  linarith

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: (10.10) `major_square_bound`
-/

namespace ArtinPrimitiveRoots

open Real Complex Filter Topology MeasureTheory Finset

namespace L102M

lemma eventually_groupReciprocalSum (a : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, 1 / 2 ≤ groupReciprocalSum x a := by
  have hm := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hlog : (1 / 2 : ℝ) < Real.log (2 / 1) := by
    rw [div_one]; have := Real.log_two_gt_d9; linarith
  have h1 := hm.eventually (eventually_gt_nhds hlog)
  have hX : Tendsto (fun x : ℝ => Real.exp (Real.log x ^ a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop)
  filter_upwards [hX.eventually h1] with x hx
  refine le_trans hx.le ?_
  unfold groupReciprocalSum primeGroup
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    refine ⟨?_, hp.2.1, ?_⟩
    · have : Real.exp (Real.log x ^ a) ^ (2 : ℝ) = Real.exp (2 * Real.log x ^ a) := by
        rw [← Real.exp_mul, mul_comm]
      rw [← this]; exact hp.1
    · have := hp.2.2
      rw [Real.rpow_one] at this
      exact this.le
  · intro p _ _
    positivity

lemma squareNorm_mul_sq (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y : ℝ)
    (hV : ∀ i, 0 < groupReciprocalSum x (a i)) :
    squareNorm x a * (4 * Y * ∏ i, groupReciprocalSum x (a i)) ^ 2 = 16 * Y ^ 2 := by
  unfold squareNorm
  have hP : (∏ i, groupReciprocalSum x (a i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hV i).ne'
  rw [Finset.prod_pow, Finset.prod_inv_distrib]
  field_simp
  ring

lemma ev_main (δ c₁ c₂ A₀ D₂ B₁ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (hD₂ : 0 < D₂) (hB₁ : 0 < B₁)
    {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 1 ≤ Real.log x ∧ (∀ i, 1 / 2 ≤ groupReciprocalSum x (a i)) ∧
      Real.log x ^ A₀ ≤ sieveLevel x ∧ Real.log x ^ (-D₂) ≤ 1 / 2 ∧
      10 * Real.exp 6 ≤ c₁ * x ∧ 4 * max c₂ 1 * x ≤ x ^ 2 ∧
      max c₂ 1 * x * Real.log x ^ B₁ ≤ x ^ 3 ∧ 2 * π ≤ Real.log x ^ B₁ ∧
      max c₂ 1 ≤ x ^ δ := by
  have hM : 0 < max c₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have e1 := eventually_ge_atTop (3 : ℝ)
  have e2 := Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)
  have e3 : ∀ᶠ x : ℝ in atTop, ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i) :=
    Filter.eventually_all.mpr fun i => eventually_groupReciprocalSum (a i) (ha i)
  have e4 : ∀ᶠ x : ℝ in atTop, Real.log x ^ A₀ ≤ sieveLevel x := by
    have h := ev_log (ev_const_mul_rpow_log_le 0 0.24 A₀ (by norm_num))
    filter_upwards [h, e2] with x hx hx1
    unfold sieveLevel
    have hL0 : 0 < Real.log x := by linarith
    rw [Real.rpow_def_of_pos hL0]
    apply Real.exp_le_exp.mpr
    rw [Real.rpow_zero, mul_one] at hx
    linarith [mul_comm (Real.log (Real.log x)) A₀]
  have e5 : ∀ᶠ x : ℝ in atTop, Real.log x ^ (-D₂) ≤ 1 / 2 := by
    have h := ev_log ((tendsto_rpow_atTop hD₂).eventually_ge_atTop (2 : ℝ))
    filter_upwards [h, e2] with x hx hx1
    have hL0 : 0 < Real.log x := by linarith
    rw [Real.rpow_neg hL0.le]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have e6 := eventually_ge_atTop (10 * Real.exp 6 / c₁)
  have e7 := eventually_ge_atTop (4 * max c₂ 1)
  have e8 : ∀ᶠ x : ℝ in atTop, Real.log x ^ B₁ ≤ x := by
    filter_upwards [ev_logpow_le_rpow B₁ 1 one_pos] with x hx
    rwa [Real.rpow_one] at hx
  have e9 := eventually_ge_atTop (max c₂ 1)
  have e10 := ev_log ((tendsto_rpow_atTop hB₁).eventually_ge_atTop (2 * π))
  have e11 := (tendsto_rpow_atTop hδ).eventually_ge_atTop (max c₂ 1)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, h10, h11⟩
  · rw [div_le_iff₀ hc₁] at h6; linarith
  · have hx0 : 0 ≤ x := by linarith
    calc 4 * max c₂ 1 * x ≤ x * x := mul_le_mul_of_nonneg_right h7 hx0
      _ = x ^ 2 := by ring
  · have hx0 : 0 ≤ x := by linarith
    calc max c₂ 1 * x * Real.log x ^ B₁ ≤ x * x * x := by
          have hLB : 0 ≤ Real.log x ^ B₁ := Real.rpow_nonneg (by linarith) _
          gcongr
      _ = x ^ 3 := by ring

/-- **The per-arc bound**, all inputs explicit. -/
theorem Gth_main (x : ℝ) {K' : ℕ} (a : Fin (K' + 1) → ℝ) (ha : 0.1 < a 0 ∧ a 0 < 0.2)
    (Y : ℝ) (hY : 1 ≤ Y) (Hm Hn : ℝ) (hHm : 0 < Hm) (hHn : 0 < Hn) (α β : ℕ → ℂ)
    (hαsupp : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm ∧ IsRough (sieveLevel x) m)
    (hβsupp : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn)
    (C : ℝ) (hαB : ∀ m, ‖α m‖ ≤ Real.log x ^ C) (hβB : ∀ n, ‖β n‖ ≤ Real.log x ^ C)
    (hL1 : 1 ≤ Real.log x) (hV : ∀ i, 1 / 2 ≤ groupReciprocalSum x (a i))
    (A₀ D A' B₁ D₂ As A Cp Lη Ksep : ℝ) (hA₀ : 0 < A₀) (hD₂0 : 0 < D₂) (hB₁1 : 1 ≤ B₁)
    (hCp : 0 ≤ Cp) (hLη0 : 0 ≤ Lη) (hKsep : 0 < Ksep)
    (hLη : ∀ y y' : ℝ, |dyadicBump y - dyadicBump y'| ≤ Lη * |y - y'|)
    (hA' : A' = 2 * D + 26 * A₀ + 4 * C + 4)
    (hB₁ : B₁ = A' + 4 * C + 3) (hD₂ : 2 * D₂ = A' + 2 * A₀ + B₁ + 4 * C + 3)
    (hAs : 2 * As = A' + 0.4 + 2 * D₂ + 2 * A₀ + B₁ + 4 * C + 3)
    (hA : 2 * A = A' + 0.4 + 2 * D₂ + 2 * A₀ + 2 * C + 1)
    (hWl : Real.log x ^ A₀ ≤ sieveLevel x)
    (hδs : Real.log x ^ (-D₂) ≤ 1 / 2)
    (hlog4X : Real.log (4 * (Hm * Hn)) ≤ 2 * Real.log x)
    (hT : 2 * π * (Hm * Hn) ≤ Hm * Hn * Real.log x ^ B₁)
    (hTx : Hm * Hn * Real.log x ^ B₁ ≤ x ^ 3)
    (hX6 : 10 * Real.exp 6 ≤ Hm * Hn)
    (hsep : ∀ X : ℝ, 10 * Real.exp 6 ≤ X → ∀ lam : ℝ,
      ∃ F : ℝ × ℝ → ℂ, Continuous F ∧
        (∀ q : ℝ × ℝ, ‖F q‖ ≤ Ksep * (1 + |lam|) ^ 4 / ((1 + q.1 ^ 2) * (1 + q.2 ^ 2))) ∧
        ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
          psiL lam (X * (w - w')) = ∫ q : ℝ × ℝ, F q *
            Complex.exp (2 * π * I * (q.1 * X * Real.log w + (q.2 - X * q.1) * Real.log w')))
    (hα' : ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ t : ℝ, |t| ≤ 2 * (Hm * Hn) * Real.log x ^ B₁ →
        ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
          α m * χ (m : ZMod k) * (m : ℂ) ^ (I * t)‖ ≤ Cp * Real.log x ^ (-A))
    (h53 : ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ Real.log x ^ C) →
      ∀ P : ℝ, 2 ≤ P → Real.log x ^ (0.1 : ℝ) ≤ Real.log P →
      Real.log P ≤ 3 * Real.log x ^ (0.2 : ℝ) →
      ∀ 𝒮 : Finset ℕ, (∀ p ∈ 𝒮, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Z : ℝ, 0 ≤ Z → Z ≤ x ^ 3 →
      ∀ M : ℝ → ℂ, Continuous M → ∀ εM : ℝ, (∀ τ : ℝ, |τ| ≤ Z → ‖M τ‖ ≤ εM) →
      ∫ τ in (-Z)..Z, ‖Pf 𝒮 P τ‖ ^ 2 * ‖M τ‖ ^ 2 *
          ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * τ)‖ ^ 2 ≤
        (Real.log x ^ (-As)) ^ 2 * (∫ τ in (-Z)..Z, ‖M τ‖ ^ 2 *
          ‖∑ n ∈ Fset Hn, c n * (n : ℂ) ^ (I * τ)‖ ^ 2) +
        4 * εM ^ 2 * (450 * Hn ^ 2 * Real.log x ^ (2 * C + 1)))
    (θ : ℝ) (hθ : θ ∈ majorArcs x A₀ Y) :
    ‖Gth x a Y Hm Hn α β θ‖ ≤
      324 * Ksep * ((172800 + 57600 * Cp ^ 2 + 11059200 * (Lη + 13) ^ 2 + 10 ^ 6) + 13824) *
        (Hm * Hn * Y ^ 2 * Real.log x ^ (-(D + 3 * A₀))) := by
  obtain ⟨_, _, k, hk1, hkL, c, _, hc⟩ := hθ
  haveI : NeZero k := ⟨by omega⟩
  have hk0 : 0 < k := by omega
  have hY0 : 0 < Y := by linarith only [hY]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith only [hL1]
  set lam := Y * (θ - c / k) with hlamdef
  have hθeq : θ = (c : ℝ) / k + lam / Y := by rw [hlamdef]; field_simp; ring
  have hlam : |lam| ≤ 2 * L ^ A₀ := by
    rw [hlamdef, abs_mul, abs_of_pos hY0]
    calc Y * |θ - c / k| ≤ Y * (2 * L ^ A₀ / Y) := by gcongr
      _ = 2 * L ^ A₀ := by field_simp
  rw [hθeq]
  obtain ⟨F, hFc, hFb, hrep⟩ := hsep (Hm * Hn) hX6 lam
  set X := Hm * Hn with hX
  have hX0 : 0 < X := mul_pos hHm hHn
  have hα0 : α 0 = 0 := by
    by_contra h; have := (hαsupp 0 h).2.2.1; simp at this
  have hβ0 : β 0 = 0 := by
    by_contra h; have := (hβsupp 0 h).1; simp at this; linarith only [this, hHn]
  have hα2 : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm := fun m h => ⟨(hαsupp m h).1, (hαsupp m h).2.1⟩
  set cU := (172800 + 57600 * Cp ^ 2 + 11059200 * (Lη + 13) ^ 2 + 10 ^ 6 : ℝ) with hcU
  set PV := ∏ i, groupReciprocalSum x (a i) with hPV
  set R := 4 * Y * PV with hR
  have hV0 : ∀ i, 0 < groupReciprocalSum x (a i) := fun i => by linarith only [hV i]
  -- the `U` side
  have hU : ∀ ρ : ZMod k × ZMod k × ZMod k, ∫ τ, ωX X τ *
      ‖Bpoly x a Y lam k ρ.1 τ * Rpoly Hm α k ρ.2.1 τ * Rpoly Hn β k ρ.2.2 τ‖ ^ 2 ≤
      R ^ 2 * X ^ 2 * (cU * L ^ (-A')) := by
    intro ρ
    have hM : ∀ τ : ℝ, |τ| ≤ X * L ^ B₁ → ‖Rpoly Hm α k ρ.2.1 τ‖ ≤ Hm * Cp * L ^ (-A) := by
      intro τ hτ
      apply Rpoly_le_of_char k Hm α _ ρ.2.1 τ
      · intro χ
        have h1 := hα' k hk0 hkL χ τ (by
          have : 0 ≤ X * L ^ B₁ := (mul_pos hX0 (Real.rpow_pos_of_pos hL0 _)).le
          linarith only [this, hτ])
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (one_div_pos.mpr hHm).le] at h1
        have h2 : 1 / Hm * ‖∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
            α m * χ (m : ZMod k) * (m : ℂ) ^ (I * τ)‖ * Hm ≤ Cp * L ^ (-A) * Hm := by
          gcongr
        rw [one_div, mul_comm (Hm⁻¹), mul_assoc, inv_mul_cancel₀ hHm.ne', mul_one] at h2
        linarith only [h2]
      · intro m hm
        exact coprime_of_rough (hαsupp m hm).2.2 hk0 (hkL.trans hWl)
    exact MU_rho x a ha Y lam hY k ρ Hm Hn hHm hHn α β hα0 hβ0 C hαB hβB hβsupp hV hL1
      A₀ A' B₁ D₂ As A Cp Lη hA₀ hCp hLη0 hLη hB₁ hB₁1 hD₂0 hD₂ hAs hA hlam hkL hδs hlog4X hT
      hTx hM h53
  -- the `V` side
  have hVv : ∀ ρ : ZMod k × ZMod k × ZMod k, ∀ σ : ℝ, ∫ τ, ωX X τ *
      ‖Bpoly x a Y lam k ρ.1 (τ - σ) * Rpoly Hm α k ρ.2.1 (τ - σ) *
        Rpoly Hn β k ρ.2.2 (τ - σ)‖ ^ 2 ≤ R ^ 2 * (13824 * X ^ 2 * L ^ (4 * C + 4)) := by
    intro ρ σ
    refine (MV_bound x a Y lam hY0 k ρ Hm Hn hHm.le hHn.le α β hα0 hβ0 (L ^ C) (L ^ C) hαB hβB
      X hX0 σ).trans ?_
    rw [← hR]
    have := MV_norm L Hm Hn C hHm.le hHn.le hL1 hlog4X
    have e : 13824 * (Hm * Hn) ^ 2 * L ^ (4 * C + 4) = 13824 * X ^ 2 * L ^ (4 * C + 4) := by
      rw [hX]
    rw [e] at this
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  set ε := L ^ ((A' + 4 * C + 4) / 2) with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hL0 _
  have hG := Gth_le x a Y Hm Hn hY0 hHm hHn α β hα2 hβsupp hα0 hβ0 lam c k
    (Ksep * (1 + |lam|) ^ 4) F hFc hFb hrep (R ^ 2 * X ^ 2 * (cU * L ^ (-A')))
    (R ^ 2 * (13824 * X ^ 2 * L ^ (4 * C + 4))) ε hε0 hU hVv
  have hsq : 0 ≤ squareNorm x a := by
    unfold squareNorm; exact Finset.prod_nonneg fun i _ => by have := hV0 i; positivity
  have hsqR : squareNorm x a * R ^ 2 = 16 * Y ^ 2 := squareNorm_mul_sq x a Y hV0
  have hcU0 : 0 ≤ cU := by positivity
  have := Gth_norm ‖Gth x a Y Hm Hn α β ((c : ℝ) / k + lam / Y)‖ (squareNorm x a) Ksep lam (k : ℝ)
    (R ^ 2 * X ^ 2 * (cU * L ^ (-A'))) (R ^ 2 * (13824 * X ^ 2 * L ^ (4 * C + 4))) L X Y R cU
    A' A₀ C D hL1 hX0 hsq hKsep.le hkR.le hcU0 hsqR hlam hkL hA₀ le_rfl le_rfl hA' hG
  exact this

end L102M

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (S : Set (ℝ × ℝ × ℝ × (ℕ → ℂ) × (ℕ → ℂ)))
    (hS : ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S →
      x ^ δ ≤ Hm ∧ x ^ δ ≤ Hn ∧ c₁ * x ≤ Hm * Hn ∧ Hm * Hn ≤ c₂ * x ∧
      (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
        ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) ∧
      (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) ∧
      (∀ m, ‖α m‖ ≤ log x ^ C) ∧ (∀ n, ‖β n‖ ≤ log x ^ C))
    (hα : ∀ A₀ B A : ℝ, 0 < A₀ → 0 < B → 0 < A →
      ∃ C' : ℝ, ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
        ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
        ∀ t : ℝ, |t| ≤ 2 * (Hm * Hn) * log x ^ B →
          ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
              α m * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)‖ ≤ C' * log x ^ (-A)) :
    ∀ A₀ : ℝ, 0 < A₀ → ∀ D : ℝ, 0 < D → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, ∀ α β : ℕ → ℂ, (x, Hm, Hn, α, β) ∈ S → x₀ ≤ x →
        ∀ Y : ℝ, 1 ≤ Y →
          ‖majorSquare x a A₀ Y Hm Hn α β‖ ≤ c * (Hm * Hn * Y * log x ^ (-D)) := by
  intro A₀ hA₀ D hD K hK a _ ha
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = 2 * D + 26 * A₀ + 4 * C + 4 := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : ℝ, B₁ = A' + 4 * C + 3 := ⟨_, rfl⟩
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : ℝ, 2 * D₂ = A' + 2 * A₀ + B₁ + 4 * C + 3 :=
    ⟨(A' + 2 * A₀ + B₁ + 4 * C + 3) / 2, by ring⟩
  obtain ⟨As, hAs⟩ : ∃ As : ℝ, 2 * As = A' + 0.4 + 2 * D₂ + 2 * A₀ + B₁ + 4 * C + 3 :=
    ⟨(A' + 0.4 + 2 * D₂ + 2 * A₀ + B₁ + 4 * C + 3) / 2, by ring⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, 2 * A = A' + 0.4 + 2 * D₂ + 2 * A₀ + 2 * C + 1 :=
    ⟨(A' + 0.4 + 2 * D₂ + 2 * A₀ + 2 * C + 1) / 2, by ring⟩
  have hA'0 : 0 < A' := by rw [hA']; positivity
  have hB₁1 : 1 ≤ B₁ := by rw [hB₁]; linarith only [hA'0, hC]
  have hB₁0 : 0 < B₁ := by linarith only [hB₁1]
  have hD₂0 : 0 < D₂ := by linarith only [hD₂, hA'0, hA₀, hB₁0, hC]
  have hAs0 : 0 < As := by linarith only [hAs, hA'0, hD₂0, hA₀, hB₁0, hC]
  have hA0 : 0 < A := by linarith only [hA, hA'0, hD₂0, hA₀, hC]
  obtain ⟨C', x₀α, hαx⟩ := hα A₀ B₁ A hA₀ hB₁0 hA0
  obtain ⟨Cp, hCp0, hCpC⟩ : ∃ Cp : ℝ, 0 ≤ Cp ∧ C' ≤ Cp := ⟨max C' 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨x₀₅₃, h53⟩ := small_prime_sparse_mean δ C As hδ hC hAs0
  obtain ⟨Ksep, hKsep, hsep⟩ := arc_cutoff_mellin_separation
  obtain ⟨Lη, hLη0, hLη⟩ := L102M.dyadicBump_lipschitz
  have hev := L102M.ev_main δ c₁ c₂ A₀ D₂ B₁ hδ hc₁ hD₂0 hB₁0 a (fun i => by linarith only [(ha i).1])
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨CG, hCG⟩ : ∃ CG : ℝ,
      CG = 324 * Ksep * ((172800 + 57600 * Cp ^ 2 + 11059200 * (Lη + 13) ^ 2 + 10 ^ 6) + 13824) :=
    ⟨_, rfl⟩
  refine ⟨16 * CG, max (max x₀α x₀₅₃) x₁, ?_⟩
  intro x Hm Hn α β hmem hx Y hY
  have hxα : x₀α ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx53 : x₀₅₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨h3, hL1, hV, hWl, hδs, h6, h4, hT3, h2π, hMδ⟩ := hx₁ x hxx₁
  obtain ⟨hHm, hHn, hc1, hc2, ⟨J, _, hJsub, hαsupp⟩, hβsupp, hαB, hβB⟩ := hS x Hm Hn α β hmem
  have hL0 : 0 < Real.log x := by linarith only [hL1]
  have hx0 : 0 < x := by linarith only [h3]
  have hxδ : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  have hHm0 : 0 < Hm := lt_of_lt_of_le hxδ hHm
  have hHn0 : 0 < Hn := lt_of_lt_of_le hxδ hHn
  have hY0 : 0 < Y := by linarith only [hY]
  have hM1 : 1 ≤ max c₂ 1 := le_max_right _ _
  have hXM : Hm * Hn ≤ max c₂ 1 * x :=
    le_trans hc2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le)
  have hHnx : Hn ≤ x := by
    have h1 : max c₂ 1 ≤ Hm := le_trans hMδ hHm
    have h2 : Hm * Hn ≤ Hm * x := le_trans hXM (mul_le_mul_of_nonneg_right h1 hx0.le)
    exact le_of_mul_le_mul_left h2 hHm0
  have hαs : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm ∧ IsRough (sieveLevel x) m := by
    intro m h
    obtain ⟨hmJ, hr⟩ := hαsupp m h
    have := hJsub hmJ
    exact ⟨this.1, this.2, hr⟩
  have hβs : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn := fun n h =>
    ⟨(hβsupp n h).1, (hβsupp n h).2.1⟩
  have hlog4X : Real.log (4 * (Hm * Hn)) ≤ 2 * Real.log x := by
    have h1 : 4 * (Hm * Hn) ≤ x ^ 2 := by
      have : 4 * (Hm * Hn) ≤ 4 * (max c₂ 1 * x) := by linarith only [hXM]
      linarith only [this, h4]
    calc Real.log (4 * (Hm * Hn)) ≤ Real.log (x ^ 2) := Real.log_le_log (by have := mul_pos hHm0 hHn0; linarith only [this]) h1
      _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
  have hT : 2 * π * (Hm * Hn) ≤ Hm * Hn * Real.log x ^ B₁ := by
    have : 0 < Hm * Hn := mul_pos hHm0 hHn0
    calc 2 * π * (Hm * Hn) = Hm * Hn * (2 * π) := by ring
      _ ≤ Hm * Hn * Real.log x ^ B₁ := mul_le_mul_of_nonneg_left h2π this.le
  have hTx : Hm * Hn * Real.log x ^ B₁ ≤ x ^ 3 := by
    have hLB : 0 ≤ Real.log x ^ B₁ := (Real.rpow_pos_of_pos hL0 _).le
    calc Hm * Hn * Real.log x ^ B₁ ≤ max c₂ 1 * x * Real.log x ^ B₁ := by gcongr
      _ ≤ x ^ 3 := hT3
  have hX6 : 10 * Real.exp 6 ≤ Hm * Hn := le_trans h6 hc1
  have hα' : ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ t : ℝ, |t| ≤ 2 * (Hm * Hn) * Real.log x ^ B₁ →
        ‖((1 / Hm : ℝ) : ℂ) * ∑ m ∈ Finset.range (⌊2 * Hm⌋₊ + 1),
          α m * χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * t)‖ ≤ Cp * Real.log x ^ (-A) := by
    intro k hk hkL χ t ht
    refine (hαx x Hm Hn α β hmem hxα k hk hkL χ t ht).trans ?_
    have : 0 ≤ Real.log x ^ (-A) := (Real.rpow_pos_of_pos hL0 _).le
    exact mul_le_mul_of_nonneg_right hCpC this
  have h53' := h53 x hx53 Hn hHn hHnx
  rw [L102M.majorSquare_eq_integral]
  have hbd : ∀ θ ∈ majorArcs x A₀ Y, ‖L102M.Gth x a Y Hm Hn α β θ‖ ≤
      CG * (Hm * Hn * Y ^ 2 * Real.log x ^ (-(D + 3 * A₀))) := by
    intro θ hθ
    rw [hCG]
    exact L102M.Gth_main x a (ha 0) Y hY Hm Hn hHm0 hHn0 α β hαs hβs C hαB hβB hL1 hV
      A₀ D A' B₁ D₂ As A Cp Lη Ksep hA₀ hD₂0 hB₁1 hCp0 hLη0 hKsep hLη hA' hB₁ hD₂ hAs hA hWl hδs
      hlog4X hT hTx hX6 hsep hα' h53' θ hθ
  have hfin : MeasureTheory.volume (majorArcs x A₀ Y) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono (L102M.majorArcs_subset x A₀ Y)) (by simp)
  have hLA : 1 ≤ Real.log x ^ A₀ := Real.one_le_rpow hL1 hA₀.le
  have hvol := L102M.volume_majorArcs_le x A₀ Y hY0 hL0 hLA
  have hCG0 : 0 ≤ CG := by rw [hCG]; positivity
  calc ‖∫ θ in majorArcs x A₀ Y, L102M.Gth x a Y Hm Hn α β θ‖
      ≤ CG * (Hm * Hn * Y ^ 2 * Real.log x ^ (-(D + 3 * A₀))) *
          MeasureTheory.volume.real (majorArcs x A₀ Y) :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hbd
    _ ≤ CG * (Hm * Hn * Y ^ 2 * Real.log x ^ (-(D + 3 * A₀))) *
          (16 * Real.log x ^ (3 * A₀) / Y) := by
        gcongr
    _ = 16 * CG * (Hm * Hn * Y * (Real.log x ^ (-(D + 3 * A₀)) * Real.log x ^ (3 * A₀))) := by
        field_simp
    _ = 16 * CG * (Hm * Hn * Y * Real.log x ^ (-D)) := by
        rw [← Real.rpow_add hL0]; congr 3; ring
end
