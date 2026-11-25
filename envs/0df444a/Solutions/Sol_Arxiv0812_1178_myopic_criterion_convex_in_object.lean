-- Prove2me | solution 1 for Arxiv0812_1178.myopic_criterion_convex_in_object
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T17:38:39.736812+00:00
-- url     : https://prove2.me/submissions/d270127d-0bcc-4df2-a74e-1bdc5243e68d

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix Arxiv0812_1178

private lemma quad_convexOn {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hMsym : Mᵀ = M) (hMpsd : ∀ w : ι → ℝ, 0 ≤ w ⬝ᵥ (M *ᵥ w)) :
    ConvexOn ℝ Set.univ (fun w : ι → ℝ => w ⬝ᵥ (M *ᵥ w)) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  simp only [smul_eq_mul]
  have hsym : v ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMsym, dotProduct_comm]
  have hexp : (a • u + b • v) ⬝ᵥ (M *ᵥ (a • u + b • v)) =
      a * a * (u ⬝ᵥ (M *ᵥ u)) + 2 * a * b * (u ⬝ᵥ (M *ᵥ v)) + b * b * (v ⬝ᵥ (M *ᵥ v)) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hsym]
    ring
  have hdiff : (u - v) ⬝ᵥ (M *ᵥ (u - v)) =
      u ⬝ᵥ (M *ᵥ u) - 2 * (u ⬝ᵥ (M *ᵥ v)) + v ⬝ᵥ (M *ᵥ v) := by
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, hsym]
    ring
  have hnonneg : 0 ≤ a * b * ((u - v) ⬝ᵥ (M *ᵥ (u - v))) :=
    mul_nonneg (mul_nonneg ha hb) (hMpsd (u - v))
  rw [hexp]
  rw [hdiff] at hnonneg
  have hcalc : a * (u ⬝ᵥ (M *ᵥ u)) + b * (v ⬝ᵥ (M *ᵥ v)) -
      (a * a * (u ⬝ᵥ (M *ᵥ u)) + 2 * a * b * (u ⬝ᵥ (M *ᵥ v)) + b * b * (v ⬝ᵥ (M *ᵥ v))) =
      a * b * (u ⬝ᵥ (M *ᵥ u) - 2 * (u ⬝ᵥ (M *ᵥ v)) + v ⬝ᵥ (M *ᵥ v)) := by
    have ha1 : a = 1 - b := by linarith
    rw [ha1]
    ring
  linarith

theorem solution {n : ℕ} (hn : 3 ≤ n) {T P : Type*} [Fintype T]
    [Fintype P] (H : T → Matrix (Baseline n) P ℂ) (ydata ybar : T → Baseline n → ℂ)
    (R : T → Matrix (Baseline n ⊕ Baseline n) (Baseline n ⊕ Baseline n) ℝ)
    (hR : ∀ t, (R t).PosDef) (α : T → Fin (n - 1) → ℝ) :
    (∃ (Q : Matrix P P ℝ) (q : P → ℝ) (c : ℝ), ∀ x : P → ℝ,
      myopicCrit H ydata ybar R x α = x ⬝ᵥ (Q *ᵥ x) + q ⬝ᵥ x + c) ∧
    ConvexOn ℝ Set.univ (fun x => myopicCrit H ydata ybar R x α) ∧
    ∀ Jprior : (P → ℝ) → ℝ, ConvexOn ℝ Set.univ Jprior →
      ConvexOn ℝ Set.univ (fun x => myopicCrit H ydata ybar R x α + Jprior x) := by
  let E : T → Baseline n → ℂ := fun t b =>
    Complex.exp (Complex.I * ((baselineOpBar n *ᵥ α t) b : ℂ))
  let A : T → Matrix (Baseline n ⊕ Baseline n) P ℝ := fun t =>
    Sum.elim (fun b p => (H t b p * E t b).re) (fun b p => (H t b p * E t b).im)
  let d : T → Baseline n ⊕ Baseline n → ℝ := fun t =>
    Sum.elim (fun b => (ydata t b - ybar t b).re) (fun b => (ydata t b - ybar t b).im)
  have hchi2 : ∀ (t : T) (x : P → ℝ),
      chi2 (ydata t) (ybar t) (R t) (myopicModel (H t) x (α t)) =
        (d t - A t *ᵥ x) ⬝ᵥ ((R t)⁻¹ *ᵥ (d t - A t *ᵥ x)) := by
    intro t x
    dsimp only [chi2]
    have hv :
        Sum.elim
          (fun b => ((ydata t - myopicModel (H t) x (α t) - ybar t) b).re)
          (fun b => ((ydata t - myopicModel (H t) x (α t) - ybar t) b).im) =
        d t - A t *ᵥ x := by
      ext s
      cases s with
      | inl b =>
        simp only [Sum.elim_inl, Pi.sub_apply, d, A, Matrix.mulVec, dotProduct, myopicModel,
          Complex.sub_re]
        have hre : ((∑ p : P, H t b p * (x p : ℂ)) * E t b).re =
            ∑ p : P, (H t b p * E t b).re * x p := by
          rw [Finset.sum_mul, Complex.re_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          have : H t b p * (x p : ℂ) * E t b = (x p : ℂ) * (H t b p * E t b) := by ring
          rw [this, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          ring
        change (ydata t b).re - ((∑ p : P, H t b p * (x p : ℂ)) * E t b).re - (ybar t b).re =
          (ydata t b).re - (ybar t b).re - ∑ p : P, (H t b p * E t b).re * x p
        rw [hre]
        ring
      | inr b =>
        simp only [Sum.elim_inr, Pi.sub_apply, d, A, Matrix.mulVec, dotProduct, myopicModel,
          Complex.sub_im]
        have him : ((∑ p : P, H t b p * (x p : ℂ)) * E t b).im =
            ∑ p : P, (H t b p * E t b).im * x p := by
          rw [Finset.sum_mul, Complex.im_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          have : H t b p * (x p : ℂ) * E t b = (x p : ℂ) * (H t b p * E t b) := by ring
          rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
          ring
        change (ydata t b).im - ((∑ p : P, H t b p * (x p : ℂ)) * E t b).im - (ybar t b).im =
          (ydata t b).im - (ybar t b).im - ∑ p : P, (H t b p * E t b).im * x p
        rw [him]
        ring
    rw [hv]
  have hRinv_sym : ∀ t, ((R t)⁻¹)ᵀ = (R t)⁻¹ := by
    intro t
    have hinv : (R t)⁻¹.PosDef := (hR t).inv
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hinv.isHermitian.eq
  have hRinv_psd : ∀ t (w : Baseline n ⊕ Baseline n → ℝ), 0 ≤ w ⬝ᵥ ((R t)⁻¹ *ᵥ w) := by
    intro t w
    have hinv : (R t)⁻¹.PosDef := (hR t).inv
    simpa using hinv.posSemidef.dotProduct_mulVec_nonneg w
  have hquad : ∃ (Q : Matrix P P ℝ) (q : P → ℝ) (c : ℝ), ∀ x : P → ℝ,
      myopicCrit H ydata ybar R x α = x ⬝ᵥ (Q *ᵥ x) + q ⬝ᵥ x + c := by
    refine ⟨∑ t : T, (A t)ᵀ * (R t)⁻¹ * A t,
      ∑ t : T, (-2 : ℝ) • ((A t)ᵀ *ᵥ ((R t)⁻¹ *ᵥ d t)),
      ∑ t : T, d t ⬝ᵥ ((R t)⁻¹ *ᵥ d t), ?_⟩
    intro x
    unfold myopicCrit
    simp_rw [hchi2]
    have hterm : ∀ t : T,
        (d t - A t *ᵥ x) ⬝ᵥ ((R t)⁻¹ *ᵥ (d t - A t *ᵥ x)) =
          x ⬝ᵥ (((A t)ᵀ * (R t)⁻¹ * A t) *ᵥ x) +
          ((-2 : ℝ) • ((A t)ᵀ *ᵥ ((R t)⁻¹ *ᵥ d t))) ⬝ᵥ x +
          d t ⬝ᵥ ((R t)⁻¹ *ᵥ d t) := by
      intro t
      have hcross1 : (A t *ᵥ x) ⬝ᵥ ((R t)⁻¹ *ᵥ d t) = ((A t)ᵀ *ᵥ ((R t)⁻¹ *ᵥ d t)) ⬝ᵥ x := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      have hcross2 : d t ⬝ᵥ ((R t)⁻¹ *ᵥ (A t *ᵥ x)) = ((A t)ᵀ *ᵥ ((R t)⁻¹ *ᵥ d t)) ⬝ᵥ x := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRinv_sym t,
          Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      have hsq : (A t *ᵥ x) ⬝ᵥ ((R t)⁻¹ *ᵥ (A t *ᵥ x)) =
          x ⬝ᵥ (((A t)ᵀ * (R t)⁻¹ * A t) *ᵥ x) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
          dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, smul_dotProduct, smul_eq_mul,
        hcross1, hcross2, hsq]
      ring
    simp_rw [hterm, Finset.sum_add_distrib]
    have hQ : x ⬝ᵥ ((∑ t : T, (A t)ᵀ * (R t)⁻¹ * A t) *ᵥ x) =
        ∑ t : T, x ⬝ᵥ (((A t)ᵀ * (R t)⁻¹ * A t) *ᵥ x) := by
      simp only [Matrix.sum_mulVec, dotProduct_sum]
    have hq : (∑ t : T, (-2 : ℝ) • ((A t)ᵀ *ᵥ ((R t)⁻¹ *ᵥ d t))) ⬝ᵥ x =
        ∑ t : T, ((-2 : ℝ) • ((A t)ᵀ *ᵥ ((R t)⁻¹ *ᵥ d t))) ⬝ᵥ x := by
      simp only [sum_dotProduct]
    rw [hQ, hq]
  have hconv : ConvexOn ℝ Set.univ (fun x => myopicCrit H ydata ybar R x α) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul, myopicCrit, hchi2]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have haff : d t - A t *ᵥ (a • x + b • y) =
        a • (d t - A t *ᵥ x) + b • (d t - A t *ᵥ y) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
      ext s
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc d t s - (a * (A t *ᵥ x) s + b * (A t *ᵥ y) s)
          = (a + b) * d t s - (a * (A t *ᵥ x) s + b * (A t *ᵥ y) s) := by rw [hab, one_mul]
        _ = a * (d t s - (A t *ᵥ x) s) + b * (d t s - (A t *ᵥ y) s) := by ring
    rw [haff]
    simpa [smul_eq_mul] using
      (quad_convexOn (R t)⁻¹ (hRinv_sym t) (hRinv_psd t)).2
        (Set.mem_univ (d t - A t *ᵥ x)) (Set.mem_univ (d t - A t *ᵥ y)) ha hb hab
  refine ⟨hquad, hconv, ?_⟩
  intro Jprior hJ
  exact hconv.add hJ
