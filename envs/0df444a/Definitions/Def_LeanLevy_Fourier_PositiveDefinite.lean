-- Prove2me | Definitions.Def_LeanLevy_Fourier_PositiveDefinite
-- name    : LeanLevy_Fourier_PositiveDefinite
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:58:58.54376+00:00
-- url     : https://prove2.me/theorems/e36083c8-481d-4ff8-9493-68bfa0c612f2
-- title:
--   LeanLevy source module: Fourier.PositiveDefinite
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.Fourier.PositiveDefinite`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/PositiveDefinite.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Definitions.Def_LeanLevy_Probability_Characteristic
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive Definite Functions on ℝ

A function `φ : ℝ → ℂ` is **positive definite** if for every finite sequence of points
`x₁, …, xₙ` and complex weights `c₁, …, cₙ`, the Hermitian form
`∑ᵢ ∑ⱼ c̄ᵢ cⱼ φ(xᵢ − xⱼ)` is nonneg (as a complex number, meaning real and `≥ 0`).

## Main definitions

* `ProbabilityTheory.IsPositiveDefinite` — the positive-definiteness predicate.

## Main results

* `IsPositiveDefinite.re_nonneg` — `.re ≥ 0` (convenience corollary of definition).
* `IsPositiveDefinite.apply_zero_nonneg` — `φ(0).re ≥ 0`.
* `IsPositiveDefinite.conj_neg` — `φ(-t) = conj(φ(t))` (Hermitianness).
* `IsPositiveDefinite.mul` — Schur product: pointwise product of PD functions is PD.
* `IsPositiveDefinite.of_charFun` — characteristic function of a probability measure is PD.
* `IsPositiveDefinite.closure_pointwise` — pointwise limit of PD functions is PD.

-/

open MeasureTheory Complex ComplexConjugate Finset Filter Topology Matrix
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

/-- A function `φ : ℝ → ℂ` is **positive definite** if for every `n`, points `x : Fin n → ℝ`,
and weights `c : Fin n → ℂ`, the Hermitian form `∑ᵢ ∑ⱼ c̄ᵢ cⱼ φ(xᵢ − xⱼ)` is
nonneg (i.e. real and `≥ 0`).

This is the standard definition from probability theory (Kallenberg, Billingsley). -/
def IsPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)

namespace IsPositiveDefinite

variable {φ ψ : ℝ → ℂ}

/-- The Hermitian form has nonneg `.re`. Convenience corollary of the definition. -/
theorem re_nonneg (hφ : IsPositiveDefinite φ) (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)).re :=
  (Complex.nonneg_iff.mp (hφ n x c)).1

/-- The Hermitian form has zero `.im`. Convenience corollary of the definition. -/
theorem im_eq_zero (hφ : IsPositiveDefinite φ) (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)).im = 0 :=
  (Complex.nonneg_iff.mp (hφ n x c)).2.symm



/-- `φ(0)` is real. -/
theorem apply_zero_im (hφ : IsPositiveDefinite φ) : (φ 0).im = 0 := by
  have h := hφ.im_eq_zero 1 (fun _ => 0) (fun _ => 1)
  simp [sub_self] at h
  exact h

/-- A PD function is Hermitian: `φ(-t) = conj(φ(t))`. -/
theorem conj_neg (hφ : IsPositiveDefinite φ) (t : ℝ) :
    φ (-t) = starRingEnd ℂ (φ t) := by
  -- Extract the 2×2 form's imaginary part being zero for any weights.
  -- Use points [0, t], so φ(0-t) = φ(-t), φ(t-0) = φ(t), φ(0-0) = φ(0), φ(t-t) = φ(0).
  have him : ∀ c₀ c₁ : ℂ,
      (starRingEnd ℂ c₀ * c₀ * φ 0 + starRingEnd ℂ c₀ * c₁ * φ (-t) +
      (starRingEnd ℂ c₁ * c₀ * φ t + starRingEnd ℂ c₁ * c₁ * φ 0)).im = 0 := by
    intro c₀ c₁
    have h := hφ.im_eq_zero 2 ![0, t] ![c₀, c₁]
    simp only [Fin.sum_univ_two] at h
    -- The h has Matrix.cons / vecHead / vecTail forms; let's normalize
    simp only [show (![0, t] : Fin 2 → ℝ) 0 = 0 from rfl,
      show (![0, t] : Fin 2 → ℝ) 1 = t from rfl,
      show (![c₀, c₁] : Fin 2 → ℂ) 0 = c₀ from rfl,
      show (![c₀, c₁] : Fin 2 → ℂ) 1 = c₁ from rfl, sub_self,
      show t - 0 = t from by ring, show 0 - t = -t from by ring] at h
    linarith
  have hφ0_im := hφ.apply_zero_im
  -- c₀ = 1, c₁ = 1: Im(φ(0) + φ(-t) + φ(t) + φ(0)) = 0
  have h11 := him 1 1
  simp only [map_one, one_mul] at h11
  have him_neg : (φ (-t)).im = -(φ t).im := by
    simp only [add_im] at h11; linarith [hφ0_im]
  -- c₀ = 1, c₁ = I gives Re(φ(-t)) = Re(φ(t))
  have hre_eq : (φ (-t)).re = (φ t).re := by
    have h1I := him 1 I
    simp only [map_one, one_mul, mul_one, conj_I] at h1I
    -- Expand to .im and compute: h1I now is (φ 0 + I * φ (-t) + (-I * φ t + -I * I * φ 0)).im = 0
    have key := h1I
    rw [show (-I * I : ℂ) = 1 from by rw [neg_mul, ← sq, I_sq, neg_neg]] at key
    simp only [add_im, mul_im, I_re, I_im, neg_im, neg_re, one_im, one_re] at key
    linarith [hφ0_im]
  apply Complex.ext
  · exact hre_eq
  · simp only [conj_im]; linarith

/-- The PD matrix is positive semidefinite. -/
theorem pdMatrix_posSemidef (hφ : IsPositiveDefinite φ) (m : ℕ) (x : Fin m → ℝ) :
    (Matrix.of fun i j : Fin m => φ (x i - x j)).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun c => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, Matrix.of_apply, star_def]
    rw [show x j - x i = -(x i - x j) from by ring, hφ.conj_neg, starRingEnd_self_apply]
  · change 0 ≤ dotProduct (star c) (mulVec (Matrix.of fun i j => φ (x i - x j)) c)
    have key : dotProduct (star c) (mulVec (Matrix.of fun i j => φ (x i - x j)) c) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j) := by
      simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
      congr 1; ext i
      rw [Finset.mul_sum]
      congr 1; ext j; ring
    rw [key]
    exact hφ m x c

/-- **Schur product theorem.** The pointwise product of two positive definite functions
is positive definite.

Proof: For fixed points `x`, the matrix `B_{ij} = ψ(xᵢ-xⱼ)` is PSD and Hermitian.
By the spectral theorem, `B_{ij} = ∑ₖ λₖ · Uᵢₖ · conj(Uⱼₖ)` with `λₖ ≥ 0`. Then
`∑ᵢⱼ c̄ᵢ cⱼ φ(xᵢ-xⱼ) ψ(xᵢ-xⱼ) = ∑ₖ λₖ · (PD form of φ with weights c·conj(U_k)) ≥ 0`. -/
theorem mul (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (fun x => φ x * ψ x) := by
  intro m x c
  simp only
  classical
  set B : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => ψ (x i - x j)
  have hB_psd : B.PosSemidef := hψ.pdMatrix_posSemidef m x
  have hB_herm : B.IsHermitian := hB_psd.isHermitian
  set ev := hB_herm.eigenvalues
  set U : Matrix (Fin m) (Fin m) ℂ := ↑hB_herm.eigenvectorUnitary
  have hev_nonneg : ∀ k, 0 ≤ ev k := fun k => hB_psd.eigenvalues_nonneg k
  -- Spectral decomposition: B i j = ∑ k, (ev k : ℂ) * U i k * conj(U j k)
  have hB_spec : ∀ i j : Fin m, B i j = ∑ k : Fin m, (↑(ev k) : ℂ) * U i k *
      starRingEnd ℂ (U j k) := by
    intro i j
    -- B = U * diag(ev) * U* by spectral theorem
    have h := hB_herm.spectral_theorem
    -- B i j = (conjStarAlgAut U (diag ev)) i j
    have hBij : B i j = ((Unitary.conjStarAlgAut ℂ _) hB_herm.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hB_herm.eigenvalues))) i j :=
      congr_fun (congr_fun h i) j
    rw [hBij, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    congr 1; ext k
    simp only [star_apply, star_def, Matrix.mul_apply, diagonal_apply, Function.comp]
    -- Need: (∑ l, U i l * if l = k then ↑(ev l) else 0) * conj(U j k)
    --     = ↑(ev k) * U i k * conj(U j k)
    -- First show the sum evaluates to U i k * ↑(hB_herm.eigenvalues k)
    -- Use calc to avoid rw bound variable issues
    -- Evaluate the sum: only the l=k term survives
    -- Use Fintype.sum_eq_single to collapse the sum
    -- (Note: we must use exact/calc to avoid rw/simp bound variable name issues)
    have key := Fintype.sum_eq_single k
      (show ∀ l : Fin m, l ≠ k →
        (↑hB_herm.eigenvectorUnitary : Matrix _ _ ℂ) i l *
        (if l = k then (↑(hB_herm.eigenvalues l) : ℂ) else 0) = 0
      from fun l hlk => by simp [hlk])
    -- key : ∑ x, f x = f k, but with possibly different bound var name
    -- Lean can match it via exact/linarith/omega but not rw/simp
    -- Use the fact that key has type about the same sum
    calc _ = (↑hB_herm.eigenvectorUnitary : Matrix _ _ ℂ) i k *
            (if k = k then (↑(hB_herm.eigenvalues k) : ℂ) else 0) *
            starRingEnd ℂ ((↑hB_herm.eigenvectorUnitary : Matrix _ _ ℂ) j k) := by
              exact congrArg (· * _) key
         _ = (↑(ev k) : ℂ) * U i k * starRingEnd ℂ (U j k) := by
              simp only [ite_true, U, ev]; ring
  -- New weights: d k i = c i * conj(U i k)
  set d : Fin m → Fin m → ℂ := fun k i => c i * starRingEnd ℂ (U i k)
  -- Algebraic identity: product form = ∑ₖ ev(k) * (PD form of φ with d k)
  -- We prove this by showing term-by-term equality after sum rearrangement.
  have hsuff : ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (φ (x i - x j) * ψ (x i - x j)) =
      ∑ k, (↑(ev k) : ℂ) *
        (∑ i, ∑ j, starRingEnd ℂ (d k i) * d k j * φ (x i - x j)) := by
    -- Substitute ψ(x i - x j) = B i j = spectral sum
    have hψ_eq : ∀ i j : Fin m, ψ (x i - x j) = B i j := fun i j => by simp [B]
    simp_rw [hψ_eq, hB_spec]
    -- LHS: ∑ i j, conj(c i) * c j * φ(x i - x j) * (∑ k, ...)
    simp_rw [Finset.mul_sum]
    -- Now: ∑ i ∑ j ∑ k, f i j k. Rearrange to ∑ k ∑ i ∑ j, f i j k.
    -- Step 1: swap j and k sums (inside ∑ i): ∑ i ∑ j ∑ k → ∑ i ∑ k ∑ j
    conv_lhs =>
      arg 2; ext i
      rw [Finset.sum_comm]
    -- Step 2: swap i and k sums: ∑ i ∑ k ... → ∑ k ∑ i ...
    rw [Finset.sum_comm]
    congr 1; ext k
    -- Goal: ∑ i, ∑ j, conj(c i) * c j * (φ(xi-xj) * (↑(ev k) * U i k * conj(U j k)))
    --     = ↑(ev k) * (∑ i, ∑ j, conj(d k i) * d k j * φ(xi-xj))
    -- Factor out ev k on the LHS and show term equality
    -- Rewrite each term and factor out ev k
    have hterm : ∀ i j : Fin m,
        starRingEnd ℂ (c i) * c j * (φ (x i - x j) * (↑(ev k) * U i k * starRingEnd ℂ (U j k)))
        = ↑(ev k) * (starRingEnd ℂ (d k i) * d k j * φ (x i - x j)) := by
      intro i j; simp only [d, map_mul, starRingEnd_self_apply]; ring
    simp_rw [hterm]
  rw [hsuff]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (by exact_mod_cast hev_nonneg k) (hφ m x (d k))



/-- For a positive definite function with `φ(0) = 1`, `‖φ(ξ)‖ ≤ 1`.

Proof sketch: Take `n = 2`, `x = (0, ξ)`, `c = (1, -φ(ξ)/‖φ(ξ)‖)`. The PD condition yields
`0 ≤ 2 - 2‖φ(ξ)‖`, hence `‖φ(ξ)‖ ≤ 1`. Requires the Hermitian symmetry `φ(-ξ) = conj(φ(ξ))`
which follows from the PD condition. -/
theorem norm_le_one (hφ : IsPositiveDefinite φ) (h0 : φ 0 = 1) (ξ : ℝ) :
    ‖φ ξ‖ ≤ 1 := by
  by_cases hξ : φ ξ = 0
  · simp [hξ]
  have hnorm_pos : (0 : ℝ) < ‖φ ξ‖ := norm_pos_iff.mpr hξ
  have hpd := hφ.re_nonneg 2 ![0, ξ] ![↑‖φ ξ‖, -(φ ξ)]
  simp only [Fin.sum_univ_two,
    show (![0, ξ] : Fin 2 → ℝ) 0 = 0 from rfl,
    show (![0, ξ] : Fin 2 → ℝ) 1 = ξ from rfl,
    show (![↑‖φ ξ‖, -(φ ξ)] : Fin 2 → ℂ) 0 = ↑‖φ ξ‖ from rfl,
    show (![↑‖φ ξ‖, -(φ ξ)] : Fin 2 → ℂ) 1 = -(φ ξ) from rfl] at hpd
  simp only [sub_self, sub_zero, zero_sub, h0, hφ.conj_neg ξ, map_neg,
    Complex.conj_ofReal, mul_neg, neg_mul, neg_neg, mul_one] at hpd
  -- hpd : 0 ≤ (↑‖φ ξ‖ * ↑‖φ ξ‖ + -(↑‖φ ξ‖ * φ ξ * conj(φ ξ))
  --     + (-(conj(φ ξ) * ↑‖φ ξ‖ * φ ξ) + conj(φ ξ) * φ ξ)).re
  -- Replace conj*z products with normSq = ‖z‖²
  have hns : φ ξ * starRingEnd ℂ (φ ξ) = ↑(Complex.normSq (φ ξ)) := by
    rw [← Complex.mul_conj]
  have hns' : starRingEnd ℂ (φ ξ) * φ ξ = ↑(Complex.normSq (φ ξ)) :=
    Complex.normSq_eq_conj_mul_self.symm
  have hns_eq : (Complex.normSq (φ ξ) : ℝ) = ‖φ ξ‖ ^ 2 := Complex.normSq_eq_norm_sq _
  -- Reassociate and replace in hpd
  have hrw1 : ↑‖φ ξ‖ * φ ξ * starRingEnd ℂ (φ ξ) =
      ↑‖φ ξ‖ * ↑(Complex.normSq (φ ξ)) := by rw [mul_assoc, hns]
  have hrw2 : starRingEnd ℂ (φ ξ) * ↑‖φ ξ‖ * φ ξ =
      ↑‖φ ξ‖ * ↑(Complex.normSq (φ ξ)) := by
    rw [show starRingEnd ℂ (φ ξ) * ↑‖φ ξ‖ * φ ξ =
        ↑‖φ ξ‖ * (starRingEnd ℂ (φ ξ) * φ ξ) from by ring, hns']
  rw [hrw1, hrw2, hns'] at hpd
  -- Now hpd only involves ↑‖φ ξ‖ and ↑(normSq (φ ξ)) — all real-valued
  -- All terms are real-valued ofReal casts, so .re extracts the real part cleanly
  -- After rewriting, hpd has form: 0 ≤ (↑a * ↑b + -(↑a * ↑c) + (-(↑a * ↑c) + ↑c)).re
  -- where a = ‖φ ξ‖, c = normSq(φ ξ). These are all ofReal products.
  -- Extract .re from each ofReal product
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at hpd
  rw [hns_eq] at hpd
  -- hpd : 0 ≤ ‖φ ξ‖ * ‖φ ξ‖ + -(‖φ ξ‖ * ‖φ ξ‖ ^ 2) + (-(‖φ ξ‖ * ‖φ ξ‖ ^ 2) + ‖φ ξ‖ ^ 2)
  -- = 2‖φ ξ‖²(1 - ‖φ ξ‖). Since ‖φ ξ‖ > 0, we get ‖φ ξ‖ ≤ 1.
  nlinarith [sq_nonneg ‖φ ξ‖, sq_nonneg (‖φ ξ‖ - 1)]

/-- The characteristic function of a probability measure is positive definite. -/
theorem of_charFun (μ : ProbabilityMeasure ℝ) :
    IsPositiveDefinite (fun ξ => charFun (μ : Measure ℝ) ξ) := by
  intro n x c
  rw [Complex.nonneg_iff]
  constructor
  · exact ProbabilityMeasure.characteristicFun_positiveSemiDefinite μ x c
  · -- The sum is real (it's the integral of normSq, which is real)
    simp only [charFun_apply_real]
    have hint : ∀ i j, Integrable
        (fun (a : ℝ) => starRingEnd ℂ (c i) * c j * exp (↑(x i - x j) * ↑a * I))
        (μ : Measure ℝ) := by
      intro i j
      apply (integrable_const (‖starRingEnd ℂ (c i) * c j‖ : ℝ)).mono'
      · exact (by fun_prop : Continuous _).aestronglyMeasurable
      · filter_upwards with a
        simp only [norm_mul,
          show (↑(x i - x j) : ℂ) * ↑a * I = ↑((x i - x j) * a) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one, le_refl]
    -- Each pointwise value is normSq(w(a)), hence real
    have hreal : ∀ a : ℝ, (∑ i, ∑ j,
        starRingEnd ℂ (c i) * c j * exp (↑(x i - x j) * ↑a * I)).im = 0 := by
      intro a
      set w : ℂ := ∑ j, c j * exp (-(↑(x j) * ↑a * I))
      suffices h : ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * exp (↑(x i - x j) * ↑a * I) =
          ↑(Complex.normSq w) by
        rw [h, Complex.ofReal_im]
      rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (↑(x i - x j) : ℂ) * ↑a * I = ↑(x i) * ↑a * I + -(↑(x j) * ↑a * I) from by
          push_cast; ring, exp_add]
      simp only [map_mul, ← exp_conj, map_neg, conj_ofReal, conj_I, mul_neg, neg_neg]
      ring
    have hF_int : Integrable (fun (a : ℝ) => ∑ i, ∑ j,
        starRingEnd ℂ (c i) * c j * exp (↑(x i - x j) * ↑a * I)) (μ : Measure ℝ) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
    have h_pull : ∀ (r : ℂ) (f : ℝ → ℂ),
        r * ∫ a, f a ∂(μ : Measure ℝ) = ∫ a, r * f a ∂(μ : Measure ℝ) :=
      fun r f => (integral_const_mul r f).symm
    simp_rw [h_pull]
    simp_rw [(integral_finsetSum Finset.univ (fun j _ => hint _ j)).symm]
    rw [(integral_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))).symm]
    rw [show (∫ (a : ℝ), ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        exp (↑(x i - x j) * ↑a * I) ∂(μ : Measure ℝ)).im =
      ∫ (a : ℝ), (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        exp (↑(x i - x j) * ↑a * I)).im ∂(μ : Measure ℝ) from
      ((@RCLike.imCLM ℂ _).integral_comp_comm hF_int).symm]
    simp only [hreal, integral_zero]

end IsPositiveDefinite



end ProbabilityTheory


