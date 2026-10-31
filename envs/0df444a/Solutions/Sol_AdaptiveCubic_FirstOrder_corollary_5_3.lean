-- Prove2me | solution 1 for AdaptiveCubic.FirstOrder.corollary_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T13:24:22.355934+00:00
-- url     : https://prove2.me/submissions/3abb1f68-33ba-49a1-abc4-0533da670c33

import Mathlib
import Definitions.Def_AdaptiveCubic_FirstOrder_IsARCSRun

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace ARC53Aux

open AdaptiveCubic.Cauchy

lemma grad_diff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (gradient f) := by
  let Φ : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun ℓ => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ℓ
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hΦ : gradient f = fun y => (LinearMap.toContinuousLinearMap Φ) (fderiv ℝ f y) := by
    funext y; rfl
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  rw [hΦ]
  exact ((LinearMap.toContinuousLinearMap Φ).contDiff.comp h1).differentiable (by norm_num)

lemma nonpos_of_deriv {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t)
    (hn : ∀ t, 0 < t → φ' t ≤ 0) (h0 : φ 0 = 0) (b : ℝ) (hb : 0 ≤ b) : φ b ≤ 0 := by
  rcases hb.eq_or_lt with h | h
  · rw [← h, h0]
  · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope φ φ' h
      (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => hd t)
    have h2 : (φ b - φ 0) / (b - 0) ≤ 0 := hceq ▸ hn c hc.1
    rw [h0, sub_zero, sub_zero] at h2
    by_contra hpos
    push Not at hpos
    have := div_pos hpos h
    linarith

lemma taylor3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f) (L : ℝ)
    (hL : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (x s : EuclideanSpace ℝ (Fin n)) :
    f (x + s) ≤ f x + ⟪s, gradient f x⟫ + 1 / 2 * ⟪s, fderiv ℝ (gradient f) x s⟫ +
      L / 6 * ‖s‖ ^ 3 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgd := grad_diff f hf
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • s) s t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const s).const_add x
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • s)) ⟪gradient f (x + t • s), s⟫ t :=
    fun t => by
      have hg := ((hd (x + t • s)).hasGradientAt).hasFDerivAt
      exact hg.comp_hasDerivAt t (hline t)
  have hG : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ⟪s, gradient f (x + t • s)⟫)
      ⟪s, fderiv ℝ (gradient f) (x + t • s) s⟫ t := fun t => by
    have h1 := (hgd (x + t • s)).hasFDerivAt.comp_hasDerivAt t (hline t)
    have h2 := ((innerSL ℝ s).hasFDerivAt).comp_hasDerivAt t h1
    simpa [Function.comp_def] using h2
  -- χ(t) ≤ 0 for t ≥ 0
  have hχ : ∀ t : ℝ, 0 ≤ t →
      ⟪s, gradient f (x + t • s)⟫ - ⟪s, gradient f x⟫ - t * ⟪s, fderiv ℝ (gradient f) x s⟫ -
        L / 2 * t ^ 2 * ‖s‖ ^ 3 ≤ 0 := by
    intro b hb
    refine nonpos_of_deriv (φ := fun t : ℝ => ⟪s, gradient f (x + t • s)⟫ - ⟪s, gradient f x⟫ -
        t * ⟪s, fderiv ℝ (gradient f) x s⟫ - L / 2 * t ^ 2 * ‖s‖ ^ 3)
      (φ' := fun t : ℝ => ⟪s, fderiv ℝ (gradient f) (x + t • s) s⟫ -
        ⟪s, fderiv ℝ (gradient f) x s⟫ - L * t * ‖s‖ ^ 3) ?_ ?_ ?_ b hb
    · intro t
      have h1 := (((hG t).sub_const ⟪s, gradient f x⟫).sub
        ((hasDerivAt_id' t).mul_const ⟪s, fderiv ℝ (gradient f) x s⟫)).sub
        (((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖s‖ ^ 3))
      exact h1.congr_deriv (by first | ring | (simp only [show (2:ℕ) - 1 = 1 from rfl, show (3:ℕ) - 1 = 2 from rfl, pow_one]; push_cast; ring))
    · intro t ht
      have h1 : ⟪s, fderiv ℝ (gradient f) (x + t • s) s⟫ - ⟪s, fderiv ℝ (gradient f) x s⟫ =
          ⟪s, (fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x) s⟫ := by
        rw [sub_apply, inner_sub_right]
      have h2 : ‖fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x‖ ≤ L * (t * ‖s‖) := by
        have := hL (x + t • s) x
        rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le] at this
      have h3 : ⟪s, (fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x) s⟫ ≤
          ‖s‖ * (‖fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x‖ * ‖s‖) :=
        le_trans (real_inner_le_norm _ _)
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      have h4 : ‖s‖ * (‖fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x‖ * ‖s‖) ≤
          ‖s‖ * ((L * (t * ‖s‖)) * ‖s‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      rw [h1]
      nlinarith
    · simp
  -- ψ(1) ≤ 0
  have hψ := nonpos_of_deriv (φ := fun t : ℝ => f (x + t • s) - f x - t * ⟪s, gradient f x⟫ -
        t ^ 2 / 2 * ⟪s, fderiv ℝ (gradient f) x s⟫ - L / 6 * t ^ 3 * ‖s‖ ^ 3)
      (φ' := fun t : ℝ => ⟪gradient f (x + t • s), s⟫ - ⟪s, gradient f x⟫ -
        t * ⟪s, fderiv ℝ (gradient f) x s⟫ - L / 2 * t ^ 2 * ‖s‖ ^ 3) ?_ ?_ ?_ 1 zero_le_one
  · simp only [one_smul, one_pow, one_mul] at hψ
    linarith
  · intro t
    have h1 := ((((hφ t).sub_const (f x)).sub
      ((hasDerivAt_id' t).mul_const ⟪s, gradient f x⟫)).sub
      (((hasDerivAt_pow 2 t).div_const 2).mul_const ⟪s, fderiv ℝ (gradient f) x s⟫)).sub
      (((hasDerivAt_pow 3 t).const_mul (L / 6)).mul_const (‖s‖ ^ 3))
    exact h1.congr_deriv (by first | ring | (simp only [show (2:ℕ) - 1 = 1 from rfl, show (3:ℕ) - 1 = 2 from rfl, pow_one]; push_cast; ring))
  · intro t ht
    have := hχ t ht.le
    rw [real_inner_comm s (gradient f (x + t • s))]
    linarith
  · simp

lemma rho_ge_one {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) (C L : ℝ)
    (htay : f (x + s) ≤ f x + ⟪s, gradient f x⟫ + 1 / 2 * ⟪s, fderiv ℝ (gradient f) x s⟫ +
      L / 6 * ‖s‖ ^ 3)
    (hAM : ‖(fderiv ℝ (gradient f) x - B) s‖ ≤ C * ‖s‖ ^ 2)
    (hσ : (3 * C + L) / 2 ≤ σ) (h26 : model f B σ x s < f x) :
    1 ≤ rho f B σ x s := by
  unfold rho
  rw [one_le_div (by linarith)]
  have h1 : ⟪s, fderiv ℝ (gradient f) x s⟫ - ⟪s, B s⟫ ≤ C * ‖s‖ ^ 3 := by
    rw [← inner_sub_right, ← sub_apply]
    calc _ ≤ ‖s‖ * ‖(fderiv ℝ (gradient f) x - B) s‖ := real_inner_le_norm _ _
      _ ≤ ‖s‖ * (C * ‖s‖ ^ 2) := mul_le_mul_of_nonneg_left hAM (norm_nonneg _)
      _ = C * ‖s‖ ^ 3 := by ring
  have h2 : 0 ≤ ‖s‖ ^ 3 := by positivity
  have h3 : (3 * C + L) / 2 * ‖s‖ ^ 3 ≤ σ * ‖s‖ ^ 3 := mul_le_mul_of_nonneg_right hσ h2
  unfold model at h26 ⊢
  linarith

lemma count_bound (F : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] (δ : ℝ)
    (hmono : ∀ k, F (k + 1) ≤ F k) (hdec : ∀ k, P k → F (k + 1) + δ ≤ F k) :
    ∀ j, (((Finset.range j).filter P).card : ℝ) * δ ≤ F 0 - F j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [Finset.sum_range_succ]
    push_cast at ih ⊢
    by_cases hP : P j
    · simp only [hP, if_true]
      linarith [hdec j hP]
    · simp only [hP, if_false]
      linarith [hmono j]

lemma finset_bound (P : ℕ → Prop) [DecidablePred P] (K : ℝ)
    (h : ∀ j, (((Finset.range j).filter P).card : ℝ) ≤ K) (t : Finset ℕ)
    (ht : ∀ k ∈ t, P k) : (t.card : ℝ) ≤ K := by
  have hsub : t ⊆ (Finset.range (t.sup id + 1)).filter P := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hk), ht k hk⟩
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (h _)

lemma int_le_ceil_of_le (a : ℕ) (K : ℝ) (h : (a : ℝ) ≤ K) : (a : ℤ) ≤ ⌈K⌉ := by
  have h3 : ((a : ℤ) : ℝ) ≤ ((⌈K⌉ : ℤ) : ℝ) := by
    rw [Int.cast_natCast]; exact le_trans h (Int.le_ceil K)
  exact_mod_cast h3

lemma set_part (P : ℕ → Prop) [DecidablePred P] (K : ℝ)
    (h : ∀ j, (((Finset.range j).filter P).card : ℝ) ≤ K) :
    {k | P k}.Finite ∧ (({k | P k}.ncard : ℤ) ≤ ⌈K⌉) := by
  have hfin : {k | P k}.Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈K⌉₊ + 1)
    have := finset_bound P K h t (fun k hk => hts hk)
    rw [htc] at this
    push_cast at this
    linarith [Nat.le_ceil K]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact int_le_ceil_of_le _ _ (finset_bound P K h hfin.toFinset (fun k hk => by simpa using hk))

lemma unsucc_bound (σ : ℕ → ℝ) (S : ℕ → Prop) [DecidablePred S] (σmin L₀ γ₁ : ℝ)
    (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k) (hle : ∀ k, σ k ≤ L₀) (hγ : 1 < γ₁)
    (hun : ∀ k, ¬ S k → γ₁ * σ k ≤ σ (k + 1)) :
    ∀ j, (((Finset.range j).filter (fun k => ¬ S k)).card : ℝ) ≤
      ((((Finset.range j).filter S).card : ℝ) + 1) * (Real.log (L₀ / σmin) / Real.log γ₁) := by
  have hpos : ∀ k, 0 < σ k := fun k => lt_of_lt_of_le hσmin (h211 k)
  have hL₀ : 0 < L₀ := lt_of_lt_of_le (hpos 0) (hle 0)
  have hD : Real.log (L₀ / σmin) = Real.log L₀ - Real.log σmin :=
    Real.log_div hL₀.ne' hσmin.ne'
  have hlg : 0 < Real.log γ₁ := Real.log_pos hγ
  have key : ∀ j, (((Finset.range j).filter (fun k => ¬ S k)).card : ℝ) * Real.log γ₁ -
      (((Finset.range j).filter S).card : ℝ) * (Real.log L₀ - Real.log σmin) ≤
      Real.log (σ j) - Real.log (σ 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.card_filter, Finset.card_filter] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast at ih ⊢
      by_cases hS : S j
      · simp only [hS, if_true, not_true_eq_false, if_false]
        have h1 : Real.log σmin ≤ Real.log (σ (j + 1)) := Real.log_le_log hσmin (h211 _)
        have h2 : Real.log (σ j) ≤ Real.log L₀ := Real.log_le_log (hpos j) (hle j)
        linarith
      · simp only [hS, if_true, not_false_eq_true, if_false]
        have h1 : Real.log (γ₁ * σ j) ≤ Real.log (σ (j + 1)) :=
          Real.log_le_log (by nlinarith [hpos j]) (hun j hS)
        rw [Real.log_mul (by linarith) (hpos j).ne'] at h1
        linarith
  intro j
  have h1 := key j
  have h2 : Real.log (σ j) ≤ Real.log L₀ := Real.log_le_log (hpos j) (hle j)
  have h3 : Real.log σmin ≤ Real.log (σ 0) := Real.log_le_log hσmin (h211 0)
  rw [← mul_div_assoc, le_div_iff₀ hlg, hD]
  linarith

lemma gtaylor {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f) (L : ℝ)
    (hL : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (x s u : EuclideanSpace ℝ (Fin n)) :
    ⟪u, gradient f (x + s)⟫ - ⟪u, gradient f x⟫ - ⟪u, fderiv ℝ (gradient f) x s⟫ ≤
      L / 2 * (‖u‖ * ‖s‖ ^ 2) := by
  have hgd := grad_diff f hf
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • s) s t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const s).const_add x
  have hG : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ⟪u, gradient f (x + t • s)⟫)
      ⟪u, fderiv ℝ (gradient f) (x + t • s) s⟫ t := fun t => by
    have h1 := (hgd (x + t • s)).hasFDerivAt.comp_hasDerivAt t (hline t)
    have h2 := ((innerSL ℝ u).hasFDerivAt).comp_hasDerivAt t h1
    simpa [Function.comp_def] using h2
  have h := nonpos_of_deriv (φ := fun t : ℝ => ⟪u, gradient f (x + t • s)⟫ - ⟪u, gradient f x⟫ -
        t * ⟪u, fderiv ℝ (gradient f) x s⟫ - L / 2 * t ^ 2 * (‖u‖ * ‖s‖ ^ 2))
      (φ' := fun t : ℝ => ⟪u, fderiv ℝ (gradient f) (x + t • s) s⟫ -
        ⟪u, fderiv ℝ (gradient f) x s⟫ - L * t * (‖u‖ * ‖s‖ ^ 2)) ?_ ?_ ?_ 1 zero_le_one
  · simp only [one_smul, one_pow, one_mul] at h
    linarith
  · intro t
    have h1 := (((hG t).sub_const ⟪u, gradient f x⟫).sub
      ((hasDerivAt_id' t).mul_const ⟪u, fderiv ℝ (gradient f) x s⟫)).sub
      (((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖u‖ * ‖s‖ ^ 2))
    exact h1.congr_deriv (by first | ring | (simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring))
  · intro t ht
    have h1 : ⟪u, fderiv ℝ (gradient f) (x + t • s) s⟫ - ⟪u, fderiv ℝ (gradient f) x s⟫ =
        ⟪u, (fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x) s⟫ := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right]
    have h2 : ‖fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x‖ ≤ L * (t * ‖s‖) := by
      have := hL (x + t • s) x
      rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le] at this
    have h3 : ⟪u, (fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x) s⟫ ≤
        ‖u‖ * (‖fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x‖ * ‖s‖) :=
      le_trans (real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    have h4 : ‖u‖ * (‖fderiv ℝ (gradient f) (x + t • s) - fderiv ℝ (gradient f) x‖ * ‖s‖) ≤
        ‖u‖ * ((L * (t * ‖s‖)) * ‖s‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    have h5 : ‖u‖ * ((L * (t * ‖s‖)) * ‖s‖) = L * t * (‖u‖ * ‖s‖ ^ 2) := by ring
    rw [h1]
    linarith
  · simp

lemma gnorm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (x s : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s‖ ≤ L / 2 * ‖s‖ ^ 2 := by
  have h := gtaylor f hf L hL x s (gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s)
  rw [← inner_sub_right, ← inner_sub_right, real_inner_self_eq_norm_sq] at h
  rcases (norm_nonneg (gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s)).eq_or_lt
    with h0 | h0
  · rw [← h0]; positivity
  · apply le_of_mul_le_mul_left _ h0
    have e1 : ‖gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s‖ ^ 2 =
        ‖gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s‖ *
        ‖gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s‖ := sq _
    have e2 : L / 2 * (‖gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s‖ * ‖s‖ ^ 2) =
        ‖gradient f (x + s) - gradient f x - fderiv ℝ (gradient f) x s‖ * (L / 2 * ‖s‖ ^ 2) := by
      ring
    linarith

lemma vec_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a b p q s : E)
    (σ κθ κH L C : ℝ) (h1 : ‖a - b - p‖ ≤ L / 2 * ‖s‖ ^ 2) (h2 : ‖p - q‖ ≤ C * ‖s‖ ^ 2)
    (h3 : ‖b + q + (σ * ‖s‖) • s‖ ≤ κθ * min 1 ‖s‖ * ‖b‖) (h4 : ‖b - a‖ ≤ κH * ‖s‖)
    (hσ : 0 ≤ σ) (hθ : 0 ≤ κθ) (hκH : 0 ≤ κH) :
    (1 - κθ) * ‖a‖ ≤ (1 / 2 * L + C + σ + κθ * κH) * ‖s‖ ^ 2 := by
  have hdec : a = (a - b - p) + (p - q) - (σ * ‖s‖) • s + (b + q + (σ * ‖s‖) • s) := by abel
  have hsm : ‖(σ * ‖s‖) • s‖ = σ * ‖s‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]; ring
  have ha : ‖a‖ ≤ ‖a - b - p‖ + ‖p - q‖ + ‖(σ * ‖s‖) • s‖ + ‖b + q + (σ * ‖s‖) • s‖ := by
    calc ‖a‖ = ‖(a - b - p) + (p - q) - (σ * ‖s‖) • s + (b + q + (σ * ‖s‖) • s)‖ := by
          rw [← hdec]
      _ ≤ ‖(a - b - p) + (p - q) - (σ * ‖s‖) • s‖ + ‖b + q + (σ * ‖s‖) • s‖ := norm_add_le _ _
      _ ≤ ‖(a - b - p) + (p - q)‖ + ‖(σ * ‖s‖) • s‖ + ‖b + q + (σ * ‖s‖) • s‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ‖a - b - p‖ + ‖p - q‖ + ‖(σ * ‖s‖) • s‖ + ‖b + q + (σ * ‖s‖) • s‖ := by
          gcongr; exact norm_add_le _ _
  have hb : ‖b‖ ≤ ‖a‖ + κH * ‖s‖ := by
    have := norm_sub_norm_le b a
    linarith
  set m := min 1 ‖s‖ with hm
  have hm0 : 0 ≤ m := le_min zero_le_one (norm_nonneg _)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hms : m ≤ ‖s‖ := min_le_right _ _
  have t1 : κθ * m * ‖b‖ ≤ κθ * m * (‖a‖ + κH * ‖s‖) :=
    mul_le_mul_of_nonneg_left hb (mul_nonneg hθ hm0)
  have t2 : κθ * m * ‖a‖ ≤ κθ * ‖a‖ := by
    have : κθ * m ≤ κθ := by
      have := mul_le_mul_of_nonneg_left hm1 hθ
      linarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have t3 : κθ * m * (κH * ‖s‖) ≤ κθ * κH * ‖s‖ ^ 2 := by
    have : m * ‖s‖ ≤ ‖s‖ * ‖s‖ := mul_le_mul_of_nonneg_right hms (norm_nonneg _)
    have h' := mul_le_mul_of_nonneg_left this (mul_nonneg hθ hκH)
    linarith
  linarith

end ARC53Aux

set_option maxHeartbeats 1000000 in
open AdaptiveCubic.FirstOrder in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCSRun f γ₁ γ₂ η₁ η₂ κθ x s σ B)
    (hAF3 : ContDiff ℝ 2 f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hxX : ∀ k, x k ∈ X) (κH : ℝ) (hκH : 1 ≤ κH)
    (hAF4 : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖)
    (L : ℝ) (hL : 0 < L)
    (hAF6 : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (C : ℝ) (hC : 0 < C)
    (hAM4 : ∀ k, ‖(fderiv ℝ (gradient f) (x k) - B k) (s k)‖ ≤ C * ‖s k‖ ^ 2)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k))
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (flow : ℝ) (hflow : ∀ k, flow ≤ f (x k))
    (ε : ℝ) (hε : 0 < ε) :
    let L₀ := max (σ 0) (3 / 2 * γ₂ * (C + L))
    let κg := Real.sqrt ((1 - κθ) / (1 / 2 * L + C + L₀ + κθ * κH))
    let αS := σmin * κg ^ 3 / 6
    let κsS := (f (x 0) - flow) / (η₁ * αS)
    let κuS := Real.log (L₀ / σmin) / Real.log γ₁
    let κS := (1 + κuS) * (2 + κsS)
    ({k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
        ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖}.Finite ∧
      ({k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
        ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖}.ncard : ℤ) ≤
        ⌈κsS * ε ^ (-(3 / 2 : ℝ))⌉) ∧
    (ε < ‖gradient f (x 0)‖ ∧ ε < ‖gradient f (x 1)‖ →
      ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
        (((Finset.range (j + 1)).filter
            (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℤ) ≤
          ⌈κsS * ε ^ (-(3 / 2 : ℝ))⌉ + 1) ∧
    (ε < ‖gradient f (x 0)‖ ∧ ε < ‖gradient f (x 1)‖ → ε ≤ 1 →
      ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
        (j : ℤ) ≤ ⌈κS * ε ^ (-(3 / 2 : ℝ))⌉) := by
  intro L₀ κg αS κsS κuS κS
  obtain ⟨hrun0, hTC, h41⟩ := hrun
  obtain ⟨hθ0, hθ1, hTCk⟩ := hTC
  obtain ⟨hγ₁, hγ₁₂, hη₁, hη₁₂, hη₂, hσ0, -, -, hxs, hσrule⟩ := hrun0
  have hκg : κg = Real.sqrt ((1 - κθ) / (1 / 2 * L + C + L₀ + κθ * κH)) := rfl
  have hα : αS = σmin * κg ^ 3 / 6 := rfl
  have hκs : κsS = (f (x 0) - flow) / (η₁ * αS) := rfl
  have hκu : κuS = Real.log (L₀ / σmin) / Real.log γ₁ := rfl
  have hκS : κS = (1 + κuS) * (2 + κsS) := rfl
  have hσpos : ∀ k, 0 < σ k := fun k => lt_of_lt_of_le hσmin (h211 k)
  have hL₀σ : σ 0 ≤ L₀ := le_max_left _ _
  have hL₀C : 3 / 2 * γ₂ * (C + L) ≤ L₀ := le_max_right _ _
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le hσ0 hL₀σ
  have hσmL : σmin ≤ L₀ := le_trans (h211 0) hL₀σ
  have hσup : ∀ k, σ (k + 1) ≤ γ₂ * σ k := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hσrule k
    have hk := hσpos k
    rcases lt_or_ge η₂ (AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k)) with h | h
    · have := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ γ₂ by linarith) hk.le
      linarith [(h1 h).2]
    · rcases lt_or_ge (AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k)) η₁ with h' | h'
      · exact (h3 h').2
      · have := mul_le_mul_of_nonneg_right hγ₁₂ hk.le
        linarith [(h2 ⟨h', h⟩).2]
  have hσle : ∀ k, σ k ≤ L₀ := by
    intro k
    induction k with
    | zero => exact hL₀σ
    | succ k ih =>
      by_cases hb : 3 / 2 * (C + L) ≤ σ k
      · have h1 : 1 ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) :=
          ARC53Aux.rho_ge_one f (B k) (σ k) (x k) (s k) C L
            (ARC53Aux.taylor3 f hAF3 L hAF6 (x k) (s k)) (hAM4 k) (by linarith) (h26 k)
        exact le_trans ((hσrule k).1 (by linarith)).2 ih
      · push Not at hb
        have : γ₂ * σ k ≤ γ₂ * (3 / 2 * (C + L)) :=
          mul_le_mul_of_nonneg_left hb.le (by linarith)
        linarith [hσup k]
  have hsucc : ∀ k, η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) →
      η₁ * (f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k)) ≤
        f (x k) - f (x (k + 1)) := by
    intro k hk
    have hD : 0 < f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by
      linarith [h26 k]
    rw [hxs k, if_pos hk]
    unfold AdaptiveCubic.Cauchy.rho at hk
    rw [le_div_iff₀ hD] at hk
    linarith
  have hmono : ∀ k, f (x (k + 1)) ≤ f (x k) := by
    intro k
    by_cases hk : η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k)
    · have h1 := hsucc k hk
      have hD : 0 < f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by
        linarith [h26 k]
      have := mul_pos hη₁ hD
      linarith
    · rw [hxs k, if_neg hk]
  have hDpos : 0 < 1 / 2 * L + C + L₀ + κθ * κH := by
    have := mul_pos hθ0 (show (0:ℝ) < κH by linarith)
    linarith
  have hκg2 : κg ^ 2 = (1 - κθ) / (1 / 2 * L + C + L₀ + κθ * κH) := by
    rw [hκg]; exact Real.sq_sqrt (div_nonneg (by linarith) hDpos.le)
  have hκgpos : 0 < κg := by
    rw [hκg]; exact Real.sqrt_pos.mpr (div_pos (by linarith) hDpos)
  have hstep : ∀ k, η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) →
      (1 - κθ) * ‖gradient f (x (k + 1))‖ ≤ (1 / 2 * L + C + L₀ + κθ * κH) * ‖s k‖ ^ 2 := by
    intro k hk
    have hx1 : x (k + 1) = x k + s k := by rw [hxs k, if_pos hk]
    have h1 := ARC53Aux.gnorm f hAF3 L hL.le hAF6 (x k) (s k)
    have h2 : ‖fderiv ℝ (gradient f) (x k) (s k) - B k (s k)‖ ≤ C * ‖s k‖ ^ 2 := by
      have := hAM4 k
      rwa [ContinuousLinearMap.sub_apply] at this
    have h4 : ‖gradient f (x k) - gradient f (x k + s k)‖ ≤ κH * ‖s k‖ := by
      have := hAF4 (x k) (hxX k) (x (k + 1)) (hxX (k + 1))
      rwa [hx1, sub_add_cancel_left, norm_neg] at this
    have h5 := ARC53Aux.vec_bound (gradient f (x k + s k)) (gradient f (x k))
      (fderiv ℝ (gradient f) (x k) (s k)) (B k (s k)) (s k) (σ k) κθ κH L C h1 h2 (hTCk k) h4
      (hσpos k).le hθ0.le (by linarith)
    rw [hx1]
    have h6 : (1 / 2 * L + C + σ k + κθ * κH) * ‖s k‖ ^ 2 ≤
        (1 / 2 * L + C + L₀ + κθ * κH) * ‖s k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hσle k]) (by positivity)
    linarith
  have hmdec : ∀ k, σ k * ‖s k‖ ^ 3 / 6 ≤
      f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by
    intro k
    obtain ⟨e1, e2⟩ := h41 k
    have e3 := real_inner_comm (gradient f (x k)) (s k)
    unfold AdaptiveCubic.Cauchy.model
    linarith
  have he3 : ε ^ (3 / 2 : ℝ) = (Real.sqrt ε) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have he3pos : 0 < ε ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hε _
  have hα0 : 0 < αS := by rw [hα]; positivity
  have hdecP : ∀ k, (η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
      ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖) →
      f (x (k + 1)) + η₁ * αS * ε ^ (3 / 2 : ℝ) ≤ f (x k) := by
    intro k hkP
    obtain ⟨hk, hmin⟩ := hkP
    have hg1 : ε < ‖gradient f (x (k + 1))‖ := lt_of_lt_of_le hmin (min_le_right _ _)
    have h1 := hstep k hk
    have h2 : κg ^ 2 * ε ≤ ‖s k‖ ^ 2 := by
      rw [hκg2, div_mul_eq_mul_div, div_le_iff₀ hDpos]
      have := mul_le_mul_of_nonneg_left hg1.le (show (0:ℝ) ≤ 1 - κθ by linarith)
      linarith
    have h3 : κg * Real.sqrt ε ≤ ‖s k‖ := by
      have : (κg * Real.sqrt ε) ^ 2 ≤ ‖s k‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hε.le]; exact h2
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp this
    have h4 : κg ^ 3 * ε ^ (3 / 2 : ℝ) ≤ ‖s k‖ ^ 3 := by
      rw [he3, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) h3 3
    have h5 := hmdec k
    have h6 := hsucc k hk
    have h7 : σmin * (κg ^ 3 * ε ^ (3 / 2 : ℝ)) ≤ σ k * ‖s k‖ ^ 3 :=
      mul_le_mul (h211 k) h4 (by positivity) (hσpos k).le
    have h8 : αS * ε ^ (3 / 2 : ℝ) ≤
        f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by
      rw [hα]; linarith
    have h9 := mul_le_mul_of_nonneg_left h8 hη₁.le
    linarith
  have hδ : 0 < η₁ * αS * ε ^ (3 / 2 : ℝ) := by positivity
  have hK : κsS * ε ^ (-(3 / 2 : ℝ)) * (η₁ * αS * ε ^ (3 / 2 : ℝ)) = f (x 0) - flow := by
    have hη₁ne := hη₁.ne'
    have hαne := hα0.ne'
    have hene := he3pos.ne'
    rw [hκs, Real.rpow_neg hε.le]
    field_simp
  have hcntP : ∀ j, (((Finset.range j).filter (fun k =>
      η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
        ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖)).card : ℝ) ≤
        κsS * ε ^ (-(3 / 2 : ℝ)) := by
    intro j
    have h1 := ARC53Aux.count_bound (fun k => f (x k)) _ _ hmono hdecP j
    have h2 := hflow j
    apply le_of_mul_le_mul_right _ hδ
    rw [hK]
    linarith
  have hS_le : ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
      (((Finset.range (j + 1)).filter (fun k =>
        η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) ≤
        κsS * ε ^ (-(3 / 2 : ℝ)) + 1 := by
    intro j hj
    have hsub : (Finset.range (j + 1)).filter (fun k =>
        η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k)) ⊆
        insert j ((Finset.range j).filter (fun k =>
          η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
            ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk.1 with h | h
      · exact Or.inr ⟨h, hk.2, lt_min (hj k (by omega)) (hj (k + 1) (by omega))⟩
      · exact Or.inl h
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le j ((Finset.range j).filter (fun k =>
          η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
            ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖))
    have h3 := hcntP j
    have h4 : (((Finset.range (j + 1)).filter (fun k =>
        η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) ≤
        (((Finset.range j).filter (fun k =>
          η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
            ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖)).card : ℝ) + 1 := by
      exact_mod_cast le_trans h1 h2
    linarith
  have hκu0 : 0 ≤ κuS := by
    rw [hκu]
    apply div_nonneg _ (Real.log_pos hγ₁).le
    apply Real.log_nonneg
    rw [le_div_iff₀ hσmin]
    linarith
  have hun := ARC53Aux.unsucc_bound σ
    (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))
    σmin L₀ γ₁ hσmin h211 hσle hγ₁ (fun k hk => ((hσrule k).2.2 (lt_of_not_ge hk)).1)
  have htotal : ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
      (j : ℝ) + 1 ≤ (κsS * ε ^ (-(3 / 2 : ℝ)) + 1) * (1 + κuS) + κuS := by
    intro j hj
    have h1 := hS_le j hj
    have h2 := hun (j + 1)
    have h3 := Finset.card_filter_add_card_filter_not (s := Finset.range (j + 1))
      (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))
    rw [Finset.card_range] at h3
    have h4 : ((j : ℝ) + 1) = (((Finset.range (j + 1)).filter (fun k =>
        η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) +
        (((Finset.range (j + 1)).filter (fun k =>
        ¬ η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) := by
      exact_mod_cast h3.symm
    rw [← hκu] at h2
    have h5 := mul_le_mul_of_nonneg_right h1 hκu0
    linarith
  refine ⟨ARC53Aux.set_part _ _ hcntP, ?_, ?_⟩
  · intro _ j hj
    have h := ARC53Aux.int_le_ceil_of_le _ _ (hS_le j hj)
    rwa [Int.ceil_add_one] at h
  · intro _ hε1 j hj
    have h1 := htotal j hj
    have he1 : 1 ≤ ε ^ (-(3 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by norm_num)
    have h2 : (1 + κuS) * 1 ≤ (1 + κuS) * ε ^ (-(3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left he1 (by linarith)
    have h3 : κS * ε ^ (-(3 / 2 : ℝ)) =
        (1 + κuS) * (κsS * ε ^ (-(3 / 2 : ℝ))) + 2 * ((1 + κuS) * ε ^ (-(3 / 2 : ℝ))) := by
      rw [hκS]; ring
    have h4 : (j : ℝ) ≤ κS * ε ^ (-(3 / 2 : ℝ)) := by linarith
    exact ARC53Aux.int_le_ceil_of_le j _ h4
