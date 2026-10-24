-- Prove2me | solution 1 for AccelVI.AVC.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:03:34.150626+00:00
-- url     : https://prove2.me/submissions/938b740f-1036-4ffd-83b7-3d97e69bed36

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting
import Theorems.Thm_AccelVI_AVC_lemma_5_2
import Theorems.Thm_AccelVI_AVC_lemma_5_3
import Theorems.Thm_AccelVI_AVC_eq_5_6

open AccelVI.AVC Matrix Filter Topology Asymptotics

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (hrev : IsReversible (LPol M pol)) (v0 v1 : S → ℝ) :
    Filter.Tendsto (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) Filter.atTop
        (nhds (valuePol M pol)) ∧
    (∀ η : ℝ, 0 < η →
      (fun s => avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 s - valuePol M pol)
        =o[Filter.atTop] (fun s => (theta M.lam + η) ^ s)) ∧
    0 < theta M.lam ∧ theta M.lam < M.lam := by
  obtain ⟨hP, hl0, hl1⟩ := hM
  have hM : M.Valid := ⟨hP, hl0, hl1⟩
  set θ := theta M.lam with hθdef
  -- (3): 0 < θ < λ
  have hk : 1 / kappa M.lam = (1 - M.lam) / (1 + M.lam) := by
    unfold kappa; field_simp
  have hk1 : 1 / kappa M.lam < 1 := by
    rw [hk, div_lt_one (by linarith)]; linarith
  have hsq1 : Real.sqrt (1 / kappa M.lam) < 1 := by
    rw [Real.sqrt_lt' one_pos]; simpa using hk1
  have hθpos : 0 < θ := by rw [hθdef]; unfold theta; linarith
  have hθlt : θ < M.lam := by
    obtain ⟨h1, h2⟩ := eq_5_6 M.lam hl0 hl1
    have h3 : 0 < Real.sqrt (1 - M.lam) * (1 - Real.sqrt (1 - M.lam ^ 2)) / Real.sqrt (1 + M.lam) :=
      div_pos h2 (Real.sqrt_pos.mpr (by linarith))
    linarith
  -- notation
  set v := avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 with hv
  set B := Bpol M pol with hB
  set d := xvec v 1 - xPi M pol with hd
  -- error representation
  have herr : ∀ s, 1 ≤ s → ‖v s - valuePol M pol‖ ≤ ‖B ^ (s - 1)‖ * ‖d‖ := by
    intro s hs
    have h52 := lemma_5_2 M hM pol hpol v0 v1 s hs
    refine le_trans ?_ (Matrix.linfty_opNorm_mulVec _ _)
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    have := congrFun h52 (Sum.inl i)
    simp only [xvec, xPi, Sum.elim_inl, Pi.add_apply] at this
    have e : (v s - valuePol M pol) i = ((B ^ (s - 1)) *ᵥ d) (Sum.inl i) := by
      simp only [Pi.sub_apply, hv, hd, hB]
      rw [this]; simp [xvec, xPi]
    rw [e]
    exact norm_le_pi_norm _ _
  -- Gelfand
  set Bc := B.map (algebraMap ℝ ℂ) with hBc
  have hρ : spectralRadius ℂ Bc = ENNReal.ofReal θ := lemma_5_3 M hM pol hpol hrev
  have hnormeq : ∀ n : ℕ, ‖B ^ n‖ = ‖Bc ^ n‖ := by
    intro n
    have : Bc ^ n = (B ^ n).map (algebraMap ℝ ℂ) := by
      rw [hBc]; exact (Matrix.map_pow B (algebraMap ℝ ℂ) n).symm
    rw [this, Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
    congr 2
    funext i
    congr 1
    funext j
    simp [Matrix.map_apply]
  have hG : Tendsto (fun n : ℕ => ‖Bc ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 θ) := by
    have h := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius Bc
    rw [hρ] at h
    have h2 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h
    simp only [Function.comp_def] at h2
    rw [ENNReal.toReal_ofReal hθpos.le] at h2
    refine h2.congr fun n => ?_
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]
  -- key bound: for every r > θ, eventually ‖B^n‖ ≤ r^n
  have hbound : ∀ r, θ < r → ∀ᶠ n : ℕ in atTop, ‖B ^ n‖ ≤ r ^ n := by
    intro r hr
    have h1 := hG.eventually (gt_mem_nhds hr)
    filter_upwards [h1, eventually_ge_atTop 1] with n hn hn1
    rw [hnormeq]
    have hn0 : n ≠ 0 := by omega
    have := Real.rpow_inv_natCast_pow (norm_nonneg (Bc ^ n)) hn0
    rw [← this]
    rw [one_div] at hn
    exact pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hn.le n
  have hrate : ∀ η : ℝ, 0 < η →
      (fun s => v s - valuePol M pol) =o[atTop] (fun s => (θ + η) ^ s) := by
    intro η hη
    set r := θ + η / 2 with hr
    have hr0 : 0 < r := by linarith
    have hO : (fun s => v s - valuePol M pol) =O[atTop] (fun s : ℕ => r ^ s) := by
      apply IsBigO.of_bound (‖d‖ / r)
      have hb' : ∀ᶠ s : ℕ in atTop, ‖B ^ (s - 1)‖ ≤ r ^ (s - 1) ∧ 1 ≤ s := by
        filter_upwards [(Filter.tendsto_sub_atTop_nat 1).eventually (hbound r (by linarith)),
          eventually_ge_atTop 1] with s h1 h2
        exact ⟨h1, h2⟩
      filter_upwards [hb'] with s ⟨h1, h2⟩
      have e1 := herr s h2
      have hrs : r ^ s = r * r ^ (s - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [Real.norm_eq_abs, abs_of_pos (pow_pos hr0 s), hrs]
      calc ‖v s - valuePol M pol‖ ≤ ‖B ^ (s - 1)‖ * ‖d‖ := e1
        _ ≤ r ^ (s - 1) * ‖d‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖d‖ / r * (r * r ^ (s - 1)) := by field_simp
    exact hO.trans_isLittleO (isLittleO_pow_pow_of_lt_left hr0.le (by linarith))
  refine ⟨?_, hrate, hθpos, hθlt⟩
  -- (1) convergence
  have hη : 0 < (1 - θ) / 2 := by linarith
  have h0 : Tendsto (fun s : ℕ => (θ + (1 - θ) / 2) ^ s) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have := (hrate _ hη).trans_tendsto h0
  exact tendsto_sub_nhds_zero_iff.mp this
