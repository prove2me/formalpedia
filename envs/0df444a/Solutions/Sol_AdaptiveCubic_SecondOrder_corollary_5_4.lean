-- Prove2me | solution 1 for AdaptiveCubic.SecondOrder.corollary_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T17:42:48.490987+00:00
-- url     : https://prove2.me/submissions/7e8d6b44-708e-4321-a6ea-c3c7722a91c2

import Mathlib
import Definitions.Def_AdaptiveCubic_SecondOrder_IsARCSRun
import Definitions.Def_AdaptiveCubic_SecondOrder_lamMin

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace ARCS54Aux

open AdaptiveCubic.Cauchy AdaptiveCubic.SecondOrder

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

lemma model_dec_curv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ ε : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) (Ls : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hσ : 0 < σ) (hε : 0 < ε) (hmin : ∀ t ∈ Ls, model f B σ x s ≤ model f B σ x t)
    (hneg : ε < -lamMin B Ls) : ε ^ 3 / (6 * σ ^ 2) ≤ f x - model f B σ x s := by
  obtain ⟨v, hvL, hv1, hvB⟩ : ∃ v, v ∈ Ls ∧ ‖v‖ = 1 ∧ ⟪B v, v⟫ < -ε := by
    unfold lamMin at hneg
    by_cases hne : Nonempty {v : EuclideanSpace ℝ (Fin n) // v ∈ Ls ∧ ‖v‖ = 1}
    · obtain ⟨⟨v, hv⟩, h⟩ := exists_lt_of_ciInf_lt
        (show (⨅ v : {v : EuclideanSpace ℝ (Fin n) // v ∈ Ls ∧ ‖v‖ = 1}, ⟪B v, v⟫) < -ε by
          linarith)
      exact ⟨v, hv.1, hv.2, h⟩
    · rw [not_nonempty_iff] at hne
      rw [Real.iInf_of_isEmpty] at hneg
      linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = -⟪B v, v⟫ := ⟨_, rfl⟩
  have hκε : ε < κ := by linarith
  have hκ0 : 0 < κ := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = κ / σ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hsym : ⟪v, B v⟫ = ⟪B v, v⟫ := real_inner_comm _ _
  have key : ∀ c : ℝ, f x - model f B σ x (c • v) =
      -(c * ⟪v, gradient f x⟫) + c ^ 2 / 2 * κ - σ / 3 * |c| ^ 3 := by
    intro c
    unfold model
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul, hv1,
      Real.norm_eq_abs, mul_one]
    rw [hκ, ← hsym]
    ring
  have hgen : ∀ c : ℝ, c * ⟪v, gradient f x⟫ ≤ 0 → |c| = t →
      ε ^ 3 / (6 * σ ^ 2) ≤ f x - model f B σ x s := by
    intro c hc habs
    have h1 := hmin (c • v) (Ls.smul_mem c hvL)
    have h2 := key c
    have hc2 : c ^ 2 = t ^ 2 := by rw [← sq_abs, habs]
    have h3 : t ^ 2 / 2 * κ - σ / 3 * t ^ 3 = κ ^ 3 / (6 * σ ^ 2) := by
      rw [ht]; field_simp; ring
    have h4 : ε ^ 3 / (6 * σ ^ 2) ≤ κ ^ 3 / (6 * σ ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ hε.le hκε.le 3
    rw [habs, hc2] at h2
    linarith
  rcases le_total 0 ⟪v, gradient f x⟫ with h | h
  · exact hgen (-t) (by nlinarith) (by rw [abs_neg, abs_of_nonneg ht0])
  · exact hgen t (by nlinarith) (abs_of_nonneg ht0)

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

end ARCS54Aux

open AdaptiveCubic.SecondOrder in
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
    (flow : ℝ) (hflow : ∀ k, flow ≤ f (x k))
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k))
    (Lsub : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hsL : ∀ k, s k ∈ Lsub k)
    (hmin : ∀ k, ∀ t ∈ Lsub k,
      AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) ≤ AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) t)
    (ε : ℝ) (hε : 0 < ε) :
    let L₀ := max (σ 0) (3 / 2 * γ₂ * (C + L))
    let αcurv := σmin / (6 * L₀ ^ 3)
    let κcurv := (f (x 0) - flow) / (η₁ * αcurv)
    let κuS := Real.log (L₀ / σmin) / Real.log γ₁
    let κtcurv := (1 + κuS) * κcurv + κuS
    (({k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧ ε < -lamMin (B k) (Lsub k)}).Finite ∧
      (({k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧ ε < -lamMin (B k) (Lsub k)}).ncard : ℤ) ≤
        ⌈κcurv * ε ^ (-3 : ℤ)⌉) ∧
    ((∃ l : ℕ, -lamMin (B l) (Lsub l) ≤ ε) ∧
      ∀ j : ℕ, (∀ k ≤ j, ε < -lamMin (B k) (Lsub k)) →
      (((Finset.range (j + 1)).filter
        (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℤ) ≤ ⌈κcurv * ε ^ (-3 : ℤ)⌉) ∧
    (ε ≤ 1 → ∀ j : ℕ, (∀ k ≤ j, ε < -lamMin (B k) (Lsub k)) →
      (j : ℤ) ≤ ⌈κtcurv * ε ^ (-3 : ℤ)⌉) := by
  intro L₀ αcurv κcurv κuS κtcurv
  obtain ⟨hrun0, -, -, -⟩ := hrun
  obtain ⟨hγ₁, hγ₁₂, hη₁, hη₁₂, hη₂, hσ0, -, -, hxs, hσrule⟩ := hrun0
  have hα : αcurv = σmin / (6 * L₀ ^ 3) := rfl
  have hκc : κcurv = (f (x 0) - flow) / (η₁ * αcurv) := rfl
  have hκu : κuS = Real.log (L₀ / σmin) / Real.log γ₁ := rfl
  have hκt : κtcurv = (1 + κuS) * κcurv + κuS := rfl
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
          ARCS54Aux.rho_ge_one f (B k) (σ k) (x k) (s k) C L (ARCS54Aux.taylor3 f hAF3 L hAF6 (x k) (s k))
            (hAM4 k) (by linarith) (h26 k)
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
  have hα0 : 0 < αcurv := by
    rw [hα]; exact div_pos hσmin (by have := pow_pos hL₀pos 3; linarith)
  have hcurv : ∀ k, ε < -lamMin (B k) (Lsub k) →
      αcurv * ε ^ 3 ≤ f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by
    intro k hk
    have h1 := ARCS54Aux.model_dec_curv f (B k) (σ k) ε (x k) (s k) (Lsub k) (hσpos k) hε (hmin k) hk
    have h2 : αcurv * ε ^ 3 ≤ ε ^ 3 / (6 * σ k ^ 2) := by
      have hσk := hσpos k
      rw [hα, div_mul_eq_mul_div, div_le_div_iff₀ (by have := pow_pos hL₀pos 3; linarith)
        (by positivity)]
      have h3 : σmin * σ k ^ 2 ≤ L₀ ^ 3 := by
        calc σmin * σ k ^ 2 ≤ σ k * σ k ^ 2 :=
              mul_le_mul_of_nonneg_right (h211 k) (by positivity)
          _ = σ k ^ 3 := by ring
          _ ≤ L₀ ^ 3 := pow_le_pow_left₀ hσk.le (hσle k) 3
      have h4 : 0 ≤ ε ^ 3 := by positivity
      have := mul_le_mul_of_nonneg_left h3 h4
      linarith
    linarith
  have hδ : 0 < η₁ * αcurv * ε ^ 3 := by
    have := mul_pos hη₁ hα0
    positivity
  have hdecP : ∀ k, (η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
      ε < -lamMin (B k) (Lsub k)) → f (x (k + 1)) + η₁ * αcurv * ε ^ 3 ≤ f (x k) := by
    intro k hk
    have h1 := hsucc k hk.1
    have h2 := hcurv k hk.2
    have h3 := mul_le_mul_of_nonneg_left h2 hη₁.le
    linarith
  have hK : κcurv * ε ^ (-3 : ℤ) * (η₁ * αcurv * ε ^ 3) = f (x 0) - flow := by
    have hη₁ne := hη₁.ne'
    have hαne := hα0.ne'
    have hεne := hε.ne'
    rw [hκc, zpow_neg, zpow_ofNat]
    field_simp
  have hcntP : ∀ j, (((Finset.range j).filter (fun k =>
      η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
        ε < -lamMin (B k) (Lsub k))).card : ℝ) ≤ κcurv * ε ^ (-3 : ℤ) := by
    intro j
    have h1 := ARCS54Aux.count_bound (fun k => f (x k)) _ _ hmono hdecP j
    have h2 := hflow j
    apply le_of_mul_le_mul_right _ hδ
    rw [hK]
    linarith
  have hS_le : ∀ j, (∀ k ≤ j, ε < -lamMin (B k) (Lsub k)) →
      (((Finset.range (j + 1)).filter (fun k =>
        η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) ≤
        κcurv * ε ^ (-3 : ℤ) := by
    intro j hj
    apply ARCS54Aux.finset_bound _ _ hcntP
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨hk.2, hj k (by omega)⟩
  have hκu0 : 0 ≤ κuS := by
    rw [hκu]
    apply div_nonneg _ (Real.log_pos hγ₁).le
    apply Real.log_nonneg
    rw [le_div_iff₀ hσmin]
    linarith
  have hun := ARCS54Aux.unsucc_bound σ (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))
    σmin L₀ γ₁ hσmin h211 hσle hγ₁ (fun k hk => ((hσrule k).2.2 (lt_of_not_ge hk)).1)
  have htotal : ∀ j, (∀ k ≤ j, ε < -lamMin (B k) (Lsub k)) →
      (j : ℝ) + 1 ≤ (1 + κuS) * (κcurv * ε ^ (-3 : ℤ)) + κuS := by
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
    nlinarith
  refine ⟨ARCS54Aux.set_part _ _ hcntP, ⟨?_, ?_⟩, ?_⟩
  · by_contra hne
    push Not at hne
    have h1 := htotal (⌈(1 + κuS) * (κcurv * ε ^ (-3 : ℤ)) + κuS⌉₊) (fun k _ => hne k)
    have h2 := Nat.le_ceil ((1 + κuS) * (κcurv * ε ^ (-3 : ℤ)) + κuS)
    linarith
  · intro j hj
    exact ARCS54Aux.int_le_ceil_of_le _ _ (hS_le j hj)
  · intro hε1 j hj
    have h1 := htotal j hj
    have hz : 1 ≤ ε ^ (-3 : ℤ) := by
      rw [zpow_neg, zpow_ofNat]
      exact (one_le_inv₀ (by positivity)).mpr (pow_le_one₀ hε.le hε1)
    have h2 : κuS ≤ κuS * ε ^ (-3 : ℤ) := le_mul_of_one_le_right hκu0 hz
    have h3 : κtcurv * ε ^ (-3 : ℤ) =
        (1 + κuS) * (κcurv * ε ^ (-3 : ℤ)) + κuS * ε ^ (-3 : ℤ) := by
      rw [hκt]; ring
    have h4 : (j : ℝ) ≤ κtcurv * ε ^ (-3 : ℤ) := by linarith
    have h5 := ARCS54Aux.int_le_ceil_of_le j _ h4
    exact h5
