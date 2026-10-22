-- Prove2me | solution 1 for AdaptiveCubic.Cauchy.corollary_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T21:16:18.34358+00:00
-- url     : https://prove2.me/submissions/404e3cbe-5cee-4cd1-9ba4-2c462e7aa66a

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

set_option autoImplicit false

open scoped RealInnerProductSpace

namespace ARCAux3e9

open AdaptiveCubic.Cauchy

lemma model_neg_smul {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (α : ℝ) (hα : 0 ≤ α) :
    model f B σ x (-(α • gradient f x)) =
      f x - α * ‖gradient f x‖ ^ 2 + α ^ 2 / 2 * ⟪gradient f x, B (gradient f x)⟫
        + σ / 3 * α ^ 3 * ‖gradient f x‖ ^ 3 := by
  unfold model
  rw [norm_neg, norm_smul, Real.norm_of_nonneg hα]
  simp only [map_neg, map_smul, inner_neg_left, inner_neg_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

lemma inner_B_le {n : ℕ} (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (κB : ℝ) (hB : ‖B‖ ≤ κB) (v : EuclideanSpace ℝ (Fin n)) :
    |⟪v, B v⟫| ≤ κB * ‖v‖ ^ 2 := by
  calc |⟪v, B v⟫| ≤ ‖v‖ * ‖B v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖B‖ * ‖v‖) := by gcongr; exact B.le_opNorm v
    _ ≤ ‖v‖ * (κB * ‖v‖) := by gcongr
    _ = κB * ‖v‖ ^ 2 := by ring

lemma cauchy_dec {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) (κB : ℝ) (hB : ‖B‖ ≤ κB)
    (hc : ∀ α : ℝ, 0 ≤ α → model f B σ x s ≤ model f B σ x (-(α • gradient f x)))
    (α : ℝ) (hα : 0 ≤ α) :
    α * ‖gradient f x‖ ^ 2 - α ^ 2 / 2 * κB * ‖gradient f x‖ ^ 2
      - σ / 3 * α ^ 3 * ‖gradient f x‖ ^ 3 ≤ f x - model f B σ x s := by
  have h1 := hc α hα
  rw [model_neg_smul f B σ x α hα] at h1
  have h2 := (abs_le.mp (inner_B_le B κB hB (gradient f x))).2
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ α ^ 2 / 2)
  nlinarith

lemma model_le_self {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (x s : EuclideanSpace ℝ (Fin n))
    (hc : ∀ α : ℝ, 0 ≤ α → model f B σ x s ≤ model f B σ x (-(α • gradient f x))) :
    model f B σ x s ≤ f x := by
  have h := hc 0 le_rfl
  rw [model_neg_smul f B σ x 0 le_rfl] at h
  simpa using h

lemma taylor_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXc : Convex ℝ X)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hxs : x + s ∈ X)
    (κH : ℝ) (hκH : 0 ≤ κH)
    (hL : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖) :
    f (x + s) - f x - ⟪s, gradient f x⟫ ≤ κH * ‖s‖ ^ 2 := by
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • s))
      ⟪gradient f (x + t • s), s⟫ t := by
    intro t
    have hline : HasDerivAt (fun t : ℝ => x + t • s) s t := by
      simpa using ((hasDerivAt_id t).smul_const s).const_add x
    have hg := ((hf (x + t • s)).hasGradientAt).hasFDerivAt
    exact hg.comp_hasDerivAt t hline
  have hcont : ContinuousOn (fun t : ℝ => f (x + t • s)) (Set.Icc 0 1) :=
    fun t _ => (hφ t).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => f (x + t • s))
    (fun t => ⟪gradient f (x + t • s), s⟫) zero_lt_one hcont (fun t _ => hφ t)
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hceq
  have hmem : x + c • s ∈ X := hXc.add_smul_mem hx hxs ⟨hc.1.le, hc.2.le⟩
  have hdiff : f (x + s) - f x - ⟪s, gradient f x⟫ =
      ⟪gradient f (x + c • s) - gradient f x, s⟫ := by
    rw [← hceq, inner_sub_left]
    congr 1
    exact real_inner_comm _ _
  rw [hdiff]
  have hLc := hL _ hmem _ hx
  have hcs : ‖(x + c • s) - x‖ ≤ ‖s‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc.1.le]
    have := norm_nonneg s
    nlinarith [hc.2]
  calc ⟪gradient f (x + c • s) - gradient f x, s⟫
      ≤ ‖gradient f (x + c • s) - gradient f x‖ * ‖s‖ := real_inner_le_norm _ _
    _ ≤ (κH * ‖s‖) * ‖s‖ := by
        gcongr
        exact le_trans hLc (mul_le_mul_of_nonneg_left hcs hκH)
    _ = κH * ‖s‖ ^ 2 := by ring

lemma very_succ {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) (η₂ κH κB : ℝ)
    (hη₂0 : 0 ≤ η₂) (hη₂ : η₂ < 1) (hκH : 1 ≤ κH) (hκB : 0 ≤ κB) (hB : ‖B‖ ≤ κB)
    (hσ : 0 < σ)
    (hc : ∀ α : ℝ, 0 ≤ α → model f B σ x s ≤ model f B σ x (-(α • gradient f x)))
    (htay : f (x + s) - f x - ⟪s, gradient f x⟫ ≤ κH * ‖s‖ ^ 2)
    (hG : 0 < ‖gradient f x‖)
    (hbig : (108 * √2 / (1 - η₂) * (κH + κB)) ^ 2 ≤ σ * ‖gradient f x‖) :
    η₂ < rho f B σ x s := by
  have hβpos : 0 < 1 - η₂ := by linarith
  have hs2 : (1.4:ℝ) ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hKpos : 0 < κH + κB := by linarith
  have hκHBpos : 0 < 108 * √2 / (1 - η₂) * (κH + κB) :=
    mul_pos (div_pos (by positivity) hβpos) hKpos
  have hβκ : (1 - η₂) * (108 * √2 / (1 - η₂) * (κH + κB)) = 108 * √2 * (κH + κB) := by
    field_simp
  have hτ2 : √(σ * ‖gradient f x‖) ^ 2 = σ * ‖gradient f x‖ := Real.sq_sqrt (by positivity)
  have hτge : 108 * √2 / (1 - η₂) * (κH + κB) ≤ √(σ * ‖gradient f x‖) :=
    Real.le_sqrt_of_sq_le hbig
  have hτpos : 0 < √(σ * ‖gradient f x‖) := lt_of_lt_of_le hκHBpos hτge
  -- abbreviations
  generalize hτdef : √(σ * ‖gradient f x‖) = τ at hτ2 hτge hτpos
  generalize hGdef : ‖gradient f x‖ = G at hG hbig hτ2
  generalize hκHBdef : 108 * √2 / (1 - η₂) * (κH + κB) = κHB at hκHBpos hβκ hτge hbig
  have hβτ : 150 * (κH + κB) ≤ (1 - η₂) * τ := by
    have h1 := mul_le_mul_of_nonneg_left hτge hβpos.le
    have h2 := mul_le_mul_of_nonneg_right hs2 hKpos.le
    linarith
  have hκBτ : 150 * κB ≤ τ := by
    have := mul_nonneg hη₂0 hτpos.le
    linarith
  -- Cauchy decrease at α = 1/(2τ)
  have hD := cauchy_dec f B σ x s κB hB hc (1 / (2 * τ)) (by positivity)
  rw [hGdef] at hD
  have hσeq : σ = τ ^ 2 / G := by field_simp; linarith
  have hexpr : τ * (1 / (2 * τ) * G ^ 2 - (1 / (2 * τ)) ^ 2 / 2 * κB * G ^ 2
      - σ / 3 * (1 / (2 * τ)) ^ 3 * G ^ 3) = G ^ 2 * (11 / 24) - κB * G ^ 2 / (8 * τ) := by
    rw [hσeq]; field_simp; ring
  have hsmall : κB * G ^ 2 / (8 * τ) ≤ G ^ 2 / 1200 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hκBτ (sq_nonneg G)
    linarith
  have hτD : 0.45 * G ^ 2 ≤ τ * (f x - model f B σ x s) := by
    have := mul_le_mul_of_nonneg_left hD hτpos.le
    rw [hexpr] at this
    linarith [sq_nonneg G]
  have hD0pos : 0 < f x - model f B σ x s := by
    have : 0 < τ * (f x - model f B σ x s) := lt_of_lt_of_le (by positivity) hτD
    exact pos_of_mul_pos_right this hτpos.le
  -- step bound
  have hml := model_le_self f B σ x s hc
  unfold model at hml
  have hsg := (abs_le.mp (abs_real_inner_le_norm s (gradient f x))).1
  have hsB := (abs_le.mp (inner_B_le B κB hB s)).1
  rw [hGdef] at hsg
  have hr0 : 0 ≤ ‖s‖ := norm_nonneg s
  generalize hrdef : ‖s‖ = r at hsg hsB hml hr0 htay
  have hcube : σ / 3 * r ^ 3 ≤ r * G + κB / 2 * r ^ 2 := by linarith
  have hr2 : σ * r ^ 2 ≤ 7 * G := by
    rcases hr0.lt_or_eq with hr | hr
    · have h1 : r * (σ * r ^ 2) ≤ r * (3 * G + 3 / 2 * κB * r) := by linarith
      have h2 : σ * r ^ 2 ≤ 3 * G + 3 / 2 * κB * r := le_of_mul_le_mul_left h1 hr
      have h3 := mul_le_mul_of_nonneg_left h2 hσ.le
      have h4 := sq_nonneg (σ * r - 3 / 2 * κB)
      have h5 : (150 * κB) ^ 2 ≤ σ * G := by
        rw [← hτ2]; exact pow_le_pow_left₀ (by positivity) hκBτ 2
      have h6 : σ * (σ * r ^ 2) ≤ σ * (7 * G) := by linarith [sq_nonneg κB]
      exact le_of_mul_le_mul_left h6 hσ
    · rw [← hr]
      calc σ * 0 ^ 2 = 0 := by ring
        _ ≤ 7 * G := by linarith
  -- N bound
  have hN : f (x + s) - model f B σ x s ≤ (κH + κB) * r ^ 2 := by
    unfold model
    rw [hrdef]
    have : 0 ≤ σ / 3 * r ^ 3 := mul_nonneg (by positivity) (pow_nonneg hr0 3)
    have := mul_le_mul_of_nonneg_right hκH (sq_nonneg r)
    have := mul_nonneg hκB (sq_nonneg r)
    linarith
  have hτN : τ ^ 2 * (f (x + s) - model f B σ x s) ≤ 7 * (κH + κB) * G ^ 2 := by
    rw [hτ2]
    have h1 := mul_le_mul_of_nonneg_left hN hσ.le
    have h2 := mul_le_mul_of_nonneg_left hr2 hKpos.le
    have h3 : σ * (f (x + s) - model f B σ x s) ≤ 7 * (κH + κB) * G := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hG.le
    linarith
  have h5 : (150 * (κH + κB)) * (0.45 * G ^ 2) ≤ ((1 - η₂) * τ) * (τ * (f x - model f B σ x s)) :=
    mul_le_mul hβτ hτD (by positivity) (by positivity)
  have hKG : 0 < (κH + κB) * G ^ 2 := by positivity
  have hlt : τ ^ 2 * (f (x + s) - model f B σ x s) < τ ^ 2 * ((1 - η₂) * (f x - model f B σ x s)) := by
    linarith
  have hlt' := lt_of_mul_lt_mul_left hlt (by positivity)
  unfold rho
  rw [lt_div_iff₀ hD0pos]
  linarith

end ARCAux3e9

open ARCAux3e9 in
open scoped RealInnerProductSpace in
open AdaptiveCubic.Cauchy in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (hf : ContDiff ℝ 1 f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hxX : ∀ k, x k ∈ X) (hxsX : ∀ k, x k + s k ∈ X)
    (κH : ℝ) (hκH : 1 ≤ κH)
    (hAF4 : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖)
    (κB : ℝ) (hκB : 0 ≤ κB) (hAM1 : ∀ k, ‖B k‖ ≤ κB)
    (flow : ℝ) (hlow : ∀ k, flow ≤ f (x k))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hg0 : ε < ‖gradient f (x 0)‖) :
    let κHB := 108 * √2 / (1 - η₂) * (κH + κB)
    let αC := (6 * √2 * max (1 + κB) (2 * max (√(σ 0)) (κHB * √γ₂)))⁻¹
    let κsC := (f (x 0) - flow) / (η₁ * αC)
    (∀ j : ℕ, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
      (((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card : ℤ) ≤ ⌈κsC * ε ^ (-2 : ℤ)⌉) ∧
    ∀ γ₃ : ℝ, 0 < γ₃ → γ₃ ≤ 1 →
      (∀ k, η₂ < rho f (B k) (σ k) (x k) (s k) → γ₃ * σ k ≤ σ (k + 1)) →
      let κuC := 1 / Real.log γ₁ * max 1 (γ₂ * κHB ^ 2 / σ 0)
      let κC := (1 - Real.log γ₃ / Real.log γ₁) * κsC + κuC
      ∀ j : ℕ, (∀ k ≤ j, ε < ‖gradient f (x k)‖) → (j : ℤ) ≤ ⌈κC * ε ^ (-2 : ℤ)⌉ := by
  intro κHB αC κsC
  obtain ⟨hγ₁, hγ₁₂, hη₁, hη₁₂, hη₂, hσ0, _hsa, hcau, hx, hσrule⟩ := hrun
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hκHBdef : κHB = 108 * √2 / (1 - η₂) * (κH + κB) := rfl
  have hαCdef : αC = (6 * √2 * max (1 + κB) (2 * max (√(σ 0)) (κHB * √γ₂)))⁻¹ := rfl
  have hκsCdef : κsC = (f (x 0) - flow) / (η₁ * αC) := rfl
  clear_value κHB αC κsC
  have hs2 : (1.4:ℝ) ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hκHBnn : 0 ≤ κHB := by
    rw [hκHBdef]
    exact mul_nonneg (div_nonneg (by positivity) (by linarith)) (by linarith)
  have he2 : ε ^ (-2 : ℤ) = (ε ^ 2)⁻¹ := by
    rw [zpow_neg]; norm_cast
  -- σ positive
  have hσpos : ∀ k, 0 < σ k := by
    intro k
    induction k with
    | zero => exact hσ0
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := hσrule k
      rcases lt_or_ge η₂ (rho f (B k) (σ k) (x k) (s k)) with h | h
      · exact (h1 h).1
      · rcases lt_or_ge (rho f (B k) (σ k) (x k) (s k)) η₁ with h' | h'
        · have := mul_pos (by linarith : (0:ℝ) < γ₁) ih
          linarith [(h3 h').1]
        · linarith [(h2 ⟨h', h⟩).1]
  -- very successful iterations
  have hvs : ∀ k, 0 < ‖gradient f (x k)‖ → κHB ^ 2 ≤ σ k * ‖gradient f (x k)‖ →
      η₂ < rho f (B k) (σ k) (x k) (s k) := by
    intro k hG hb
    rw [hκHBdef] at hb
    exact very_succ f (B k) (σ k) (x k) (s k) η₂ κH κB (by linarith) hη₂ hκH hκB (hAM1 k)
      (hσpos k) (hcau k)
      (taylor_bound f hdiff X hXc (x k) (s k) (hxX k) (hxsX k) κH (by linarith) hAF4) hG hb
  -- σ upper bound
  have hσup : ∀ k, σ (k + 1) ≤ γ₂ * σ k := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hσrule k
    have hk := hσpos k
    rcases lt_or_ge η₂ (rho f (B k) (σ k) (x k) (s k)) with h | h
    · have := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ γ₂ by linarith) hk.le
      linarith [(h1 h).2]
    · rcases lt_or_ge (rho f (B k) (σ k) (x k) (s k)) η₁ with h' | h'
      · exact (h3 h').2
      · have := mul_le_mul_of_nonneg_right hγ₁₂ hk.le
        linarith [(h2 ⟨h', h⟩).2]
  have hσle : ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) → ∀ i ≤ j + 1,
      σ i ≤ max (σ 0) (γ₂ * κHB ^ 2 / ε) := by
    intro j hj i hi
    induction i with
    | zero => exact le_max_left _ _
    | succ i ih =>
      have hi' : i ≤ j := by omega
      have ih := ih (by omega)
      have hGi := hj i hi'
      have hGpos : 0 < ‖gradient f (x i)‖ := lt_trans hε hGi
      by_cases hb : κHB ^ 2 ≤ σ i * ‖gradient f (x i)‖
      · exact le_trans ((hσrule i).1 (hvs i hGpos hb)).2 ih
      · push Not at hb
        have h1 : σ i * ε < κHB ^ 2 :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left hGi.le (hσpos i).le) hb
        have h2 : γ₂ * σ i ≤ γ₂ * κHB ^ 2 / ε := by
          rw [mul_div_assoc]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [le_div_iff₀ hε]; linarith
        exact le_trans (hσup i) (le_trans h2 (le_max_right _ _))
  -- Q and its properties
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = max (1 + κB) (2 * max (√(σ 0)) (κHB * √γ₂)) := ⟨_, rfl⟩
  rw [← hQ] at hαCdef
  have hQ1 : 1 + κB ≤ Q := hQ ▸ le_max_left _ _
  have hQ2 : 2 * max (√(σ 0)) (κHB * √γ₂) ≤ Q := hQ ▸ le_max_right _ _
  have hQpos : 0 < Q := by linarith
  have hQσ : 4 * σ 0 ≤ Q ^ 2 := by
    have h : 2 * √(σ 0) ≤ Q := le_trans (by linarith [le_max_left (√(σ 0)) (κHB * √γ₂)]) hQ2
    have h' := pow_le_pow_left₀ (by positivity) h 2
    have h'' : (2 * √(σ 0)) ^ 2 = 4 * σ 0 := by rw [mul_pow, Real.sq_sqrt hσ0.le]; norm_num
    linarith
  have hQκ : 4 * (γ₂ * κHB ^ 2) ≤ Q ^ 2 := by
    have h : 2 * (κHB * √γ₂) ≤ Q := le_trans (by linarith [le_max_right (√(σ 0)) (κHB * √γ₂)]) hQ2
    have h0 : 0 ≤ κHB * √γ₂ := mul_nonneg hκHBnn (Real.sqrt_nonneg _)
    have h' := pow_le_pow_left₀ (by positivity) h 2
    have h'' : (2 * (κHB * √γ₂)) ^ 2 = 4 * (γ₂ * κHB ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ γ₂ by linarith)]; ring
    linarith
  have hαCpos : 0 < αC := by rw [hαCdef]; positivity
  -- decrease on a successful iteration
  have hdec : ∀ k, ε < ‖gradient f (x k)‖ → σ k ≤ max (σ 0) (γ₂ * κHB ^ 2 / ε) →
      αC * ε ^ 2 ≤ f (x k) - model f (B k) (σ k) (x k) (s k) := by
    intro k hGk hσk
    have hGpos : 0 < ‖gradient f (x k)‖ := lt_trans hε hGk
    have hD := cauchy_dec f (B k) (σ k) (x k) (s k) κB (hAM1 k) (hcau k)
      (ε / Q / ‖gradient f (x k)‖) (by positivity)
    generalize ‖gradient f (x k)‖ = G at hD hGk hGpos
    generalize f (x k) - model f (B k) (σ k) (x k) (s k) = D at hD ⊢
    have hσk0 := hσpos k
    generalize σ k = σk at hD hσk hσk0
    have hsimp : ε / Q / G * G ^ 2 - (ε / Q / G) ^ 2 / 2 * κB * G ^ 2
        - σk / 3 * (ε / Q / G) ^ 3 * G ^ 3
        = (ε / Q) * G - (ε / Q) ^ 2 * κB / 2 - σk * (ε / Q) ^ 3 / 3 := by
      field_simp
    rw [hsimp] at hD
    have he0 : 0 ≤ ε / Q := by positivity
    have h1 : ε / Q * κB ≤ G := by
      have : ε / Q * (1 + κB) ≤ ε / Q * Q := mul_le_mul_of_nonneg_left hQ1 he0
      rw [div_mul_cancel₀ _ hQpos.ne'] at this
      linarith
    have h4σε : 4 * σk * ε ≤ Q ^ 2 := by
      rcases le_max_iff.mp hσk with h | h
      · have h1 := mul_le_mul_of_nonneg_right h hε.le
        have h2 := mul_le_mul_of_nonneg_left hε1 hσ0.le
        linarith
      · rw [le_div_iff₀ hε] at h; linarith
    have h2 : 4 * σk * (ε / Q) ^ 2 ≤ G := by
      rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      have a := mul_le_mul_of_nonneg_right h4σε hε.le
      have b := mul_le_mul_of_nonneg_left hGk.le (sq_nonneg Q)
      linarith
    have hmain : 5 / 12 * (ε / Q * G) ≤ D := by
      linarith [mul_le_mul_of_nonneg_left h1 he0, mul_le_mul_of_nonneg_left h2 he0]
    have hεG : ε / Q * ε ≤ ε / Q * G := mul_le_mul_of_nonneg_left hGk.le he0
    have hαC : αC * ε ^ 2 ≤ 5 / 12 * (ε / Q * ε) := by
      rw [hαCdef]
      have h6 : 0 < 6 * √2 * Q := by positivity
      rw [inv_mul_eq_div, div_le_iff₀ h6]
      have : 5 / 12 * (ε / Q * ε) * (6 * √2 * Q) = 5 / 2 * √2 * ε ^ 2 := by
        field_simp; ring
      rw [this]
      have := mul_le_mul_of_nonneg_right hs2 (sq_nonneg ε)
      linarith [sq_nonneg ε]
    linarith
  -- telescoping over successful iterations
  have hsum : ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) → ∀ i ≤ j + 1,
      f (x i) + η₁ * αC * ε ^ 2 *
        (((Finset.range i).filter (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card : ℝ)
        ≤ f (x 0) := by
    intro j hj i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hi' : i ≤ j := by omega
      have ih := ih (by omega)
      rw [Finset.card_filter] at ih ⊢
      rw [Finset.sum_range_succ]
      push_cast at ih ⊢
      by_cases hsucc : η₁ ≤ rho f (B i) (σ i) (x i) (s i)
      · rw [if_pos hsucc]
        have hxi : x (i + 1) = x i + s i := by rw [hx i, if_pos hsucc]
        have hdi := hdec i (hj i hi') (hσle j hj i (by omega))
        have hDpos : 0 < f (x i) - model f (B i) (σ i) (x i) (s i) :=
          lt_of_lt_of_le (by positivity) hdi
        have hr := hsucc
        unfold rho at hr
        rw [le_div_iff₀ hDpos] at hr
        rw [hxi]
        have := mul_le_mul_of_nonneg_left hdi hη₁.le
        push_cast
        linarith
      · rw [if_neg hsucc]
        have hxi : x (i + 1) = x i := by rw [hx i, if_neg hsucc]
        rw [hxi]
        push_cast
        linarith
  have hcount : ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
      (((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card : ℝ) ≤ κsC * ε ^ (-2 : ℤ) := by
    intro j hj
    have h := hsum j hj (j + 1) le_rfl
    have hl := hlow (j + 1)
    rw [he2, hκsCdef]
    have hc : 0 < η₁ * αC * ε ^ 2 := by positivity
    have heq : (f (x 0) - flow) / (η₁ * αC) * (ε ^ 2)⁻¹ = (f (x 0) - flow) / (η₁ * αC * ε ^ 2) := by
      field_simp
    rw [heq, le_div_iff₀ hc]
    linarith
  refine ⟨?_, ?_⟩
  · intro j hj
    have h := hcount j hj
    have h2 := Int.le_ceil (κsC * ε ^ (-2 : ℤ))
    exact_mod_cast le_trans h h2
  · intro γ₃ hγ₃ hγ₃1 hvs3 κuC κC j hj
    have hκuCdef : κuC = 1 / Real.log γ₁ * max 1 (γ₂ * κHB ^ 2 / σ 0) := rfl
    have hκCdef : κC = (1 - Real.log γ₃ / Real.log γ₁) * κsC + κuC := rfl
    clear_value κuC κC
    -- lower bound on σ
    have hlowσ : ∀ i, σ 0 * γ₃ ^ (((Finset.range i).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card) *
          γ₁ ^ (((Finset.range i).filter
          (fun k => ¬ η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card) ≤ σ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ,
          Finset.sum_range_succ]
        rw [Finset.card_filter, Finset.card_filter] at ih
        obtain ⟨h1, h2, h3⟩ := hσrule i
        have hσi := hσpos i
        by_cases hsucc : η₁ ≤ rho f (B i) (σ i) (x i) (s i)
        · rw [if_pos hsucc, if_neg (not_not.mpr hsucc), add_zero, pow_succ]
          have hstep : γ₃ * σ i ≤ σ (i + 1) := by
            rcases lt_or_ge η₂ (rho f (B i) (σ i) (x i) (s i)) with h | h
            · exact hvs3 i h
            · have := mul_le_mul_of_nonneg_right hγ₃1 hσi.le
              linarith [(h2 ⟨hsucc, h⟩).1]
          have := mul_le_mul_of_nonneg_left ih hγ₃.le
          linarith
        · rw [if_neg hsucc, if_pos hsucc, add_zero, pow_succ]
          have hstep : γ₁ * σ i ≤ σ (i + 1) := (h3 (lt_of_not_ge hsucc)).1
          have := mul_le_mul_of_nonneg_left ih (by linarith : (0:ℝ) ≤ γ₁)
          linarith
    have hS := hcount j hj
    have hL := hlowσ (j + 1)
    have hSU := Finset.card_filter_add_card_filter_not
      (s := Finset.range (j + 1)) (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))
    rw [Finset.card_range] at hSU
    beta_reduce at hSU
    generalize hSdef : ((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card = S at hS hL hSU
    generalize hUdef : ((Finset.range (j + 1)).filter
          (fun k => ¬ η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card = U at hL hSU
    have hM := hσle j hj (j + 1) le_rfl
    set C := max 1 (γ₂ * κHB ^ 2 / σ 0) with hC
    have hC1 : 1 ≤ C := le_max_left _ _
    have hMC : max (σ 0) (γ₂ * κHB ^ 2 / ε) ≤ σ 0 * (C / ε) := by
      apply max_le
      · rw [mul_div_assoc', le_div_iff₀ hε]
        have h1 := mul_le_mul_of_nonneg_left hε1 hσ0.le
        have h2 := mul_le_mul_of_nonneg_left hC1 hσ0.le
        linarith
      · rw [mul_div_assoc', div_le_div_iff_of_pos_right hε]
        have : γ₂ * κHB ^ 2 / σ 0 ≤ C := le_max_right _ _
        rw [div_le_iff₀ hσ0] at this; linarith
    have hpos : 0 < σ 0 * γ₃ ^ S * γ₁ ^ U := by
      have := pow_pos hγ₃ S; have := pow_pos (by linarith : (0:ℝ) < γ₁) U; positivity
    have hlog := Real.log_le_log hpos (le_trans hL (le_trans hM hMC))
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow, Real.log_mul (by positivity)
      (by positivity)] at hlog
    have hlogCε := Real.log_le_sub_one_of_pos (show 0 < C / ε by positivity)
    have hCε : C / ε ≤ C * (ε ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      have := mul_le_mul_of_nonneg_left hε1 hε.le
      rw [sq]; linarith
    have hLpos : 0 < Real.log γ₁ := Real.log_pos hγ₁
    have hl3 : Real.log γ₃ ≤ 0 := Real.log_nonpos hγ₃.le hγ₃1
    have hU : (U : ℝ) * Real.log γ₁ ≤ C * (ε ^ 2)⁻¹ - S * Real.log γ₃ := by linarith
    rw [he2] at hS ⊢
    have hgoal : (j : ℝ) ≤ κC * (ε ^ 2)⁻¹ := by
      have hjSU : (j : ℝ) + 1 = S + U := by exact_mod_cast hSU.symm
      have hkey : Real.log γ₁ * (κC * (ε ^ 2)⁻¹) =
          (Real.log γ₁ - Real.log γ₃) * (κsC * (ε ^ 2)⁻¹) + C * (ε ^ 2)⁻¹ := by
        rw [hκCdef, hκuCdef]; field_simp
      have hm := mul_le_mul_of_nonneg_left hS (by linarith : (0:ℝ) ≤ Real.log γ₁ - Real.log γ₃)
      have hLj : Real.log γ₁ * (j : ℝ) = Real.log γ₁ * S + Real.log γ₁ * U - Real.log γ₁ := by
        rw [show (j : ℝ) = S + U - 1 by linarith]; ring
      have : Real.log γ₁ * (j : ℝ) ≤ Real.log γ₁ * (κC * (ε ^ 2)⁻¹) := by
        rw [hkey]; linarith
      exact le_of_mul_le_mul_left this hLpos
    have h2 := Int.le_ceil (κC * (ε ^ 2)⁻¹)
    exact_mod_cast le_trans hgoal h2
