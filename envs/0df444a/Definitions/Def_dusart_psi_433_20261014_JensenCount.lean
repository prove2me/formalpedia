-- Prove2me | Definitions.Def_dusart_psi_433_20261014_JensenCount
-- name    : dusart_psi_433_20261014_JensenCount
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:19:16.8477+00:00
-- url     : https://prove2.me/theorems/b883c13e-cec1-4b97-850a-4ee33dcc55f1
-- title:
--   Dusart smoothing: Jensen Count
-- statement:
--   This module gives the complete jensen count component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

/- Adapted from accepted proof 464e7035-3ffd-4a20-bf03-895c7db99482.
Copyright (c) 2026 Anthropic, PBC. Apache-2.0.
The Jensen inequality is supplied directly by Mathlib, and its raw bound is retained. -/
import Definitions.Def_dusart_psi_433_20261014_Jensen
import Definitions.Def_dusart_psi_433_20261014_ZetaCenter
open Complex Set Metric
noncomputable section
namespace DusartSmoothing.RvM

def symZeta (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + T * I) + riemannZeta (z - T * I)) / 2
def reZeroSet (T : ℝ) : Set ℝ :=
  {σ | σ ∈ Icc (1 / 2 : ℝ) 2 ∧ (riemannZeta ((σ:ℂ) + T * I)).re = 0}

lemma one_third_lt_two_sub_pi_sq_div_six : (1/3:ℝ) < 2 - Real.pi^2/6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

lemma ne_one_of_im_large {T : ℝ} {z : ℂ} (hT : 4 ≤ T) (hz : ‖z‖ ≤ 2) :
    z + 2 + T * I ≠ 1 ∧ z + 2 - T * I ≠ 1 := by
  constructor <;> intro h
  · have h1 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, Complex.one_im, Complex.im_ofNat] at h1
    have := Complex.abs_im_le_norm z
    have := abs_le.mp (this.trans hz)
    linarith [this.1, this.2]
  · have h1 := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, Complex.one_im, Complex.im_ofNat] at h1
    have := Complex.abs_im_le_norm z
    have := abs_le.mp (this.trans hz)
    linarith [this.1, this.2]

lemma symZeta_analyticAt {T : ℝ} {z : ℂ} (h1 : z + T * I ≠ 1) (h2 : z - T * I ≠ 1) :
    AnalyticAt ℂ (symZeta T) z := by
  unfold symZeta
  have ha : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z + T * I)) z := by
    have hζ : AnalyticAt ℂ riemannZeta ((fun z : ℂ => z + T * I) z) :=
      analyticOnNhd_riemannZeta (S := ({1}ᶜ : Set ℂ)) (by simp) _ h1
    exact hζ.comp_of_eq (by fun_prop) rfl
  have hb : AnalyticAt ℂ (fun z : ℂ => riemannZeta (z - T * I)) z := by
    have hζ : AnalyticAt ℂ riemannZeta ((fun z : ℂ => z - T * I) z) :=
      analyticOnNhd_riemannZeta (S := ({1}ᶜ : Set ℂ)) (by simp) _ h2
    exact hζ.comp_of_eq (by fun_prop) rfl
  exact (ha.add hb).div_const

/-- for real σ (and σ + iT ≠ 1), g_T(σ) is the real number Re ζ(σ + iT). -/
lemma symZeta_ofReal {T : ℝ} (σ : ℝ) (h1 : (σ:ℂ) + T * I ≠ 1) :
    symZeta T σ = (((riemannZeta ((σ:ℂ) + T * I)).re : ℝ) : ℂ) := by
  unfold symZeta
  have hconj : riemannZeta ((σ:ℂ) - T * I) = (starRingEnd ℂ) (riemannZeta ((σ:ℂ) + T * I)) := by
    have h := riemannZeta_conj (s := (σ:ℂ) + T * I)
    have e : (starRingEnd ℂ) ((σ:ℂ) + T * I) = (σ:ℂ) - T * I := by
      simp [Complex.ext_iff]
    rw [e] at h
    exact h
  rw [hconj, Complex.add_conj]
  push_cast
  ring





lemma reZeroSet_card_raw {A C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A) :
    ∀ T : ℝ, 4 ≤ T → (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ)
      ≤ Real.log (3 * C * (T + 5) ^ max A 0) / Real.log ((0.9 : ℝ) / 0.8) := by
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  set r : ℝ := 0.8 with hr
  set R : ℝ := 0.9 with hR
  have hlogRr : 0 < Real.log (R / r) := Real.log_pos (by norm_num [hr, hR])
  intro T hT
  set κ : ℂ := ((19/10 : ℝ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ]
  have hnormκ : ‖κ‖ = 1.9 := by simp [hκ]; norm_num
  -- the centre value g_T(2) = Re ζ(2+iT) ≥ 2 − π²/6 > 1/3
  have hne2 : (2:ℂ) + T * I ≠ 1 := by
    have := ne_one_of_im_large (T := T) (z := 0) hT (by norm_num)
    simpa using this.1
  have hsub1 := norm_riemannZeta_sub_one_le (s := 2 + T * I) (by simp)
  have hre2 : 2 - Real.pi ^ 2 / 6 ≤ (riemannZeta (2 + T * I)).re := by
    have h2 : |(riemannZeta (2 + T * I) - 1).re| ≤ Real.pi ^ 2 / 6 - 1 :=
      (Complex.abs_re_le_norm _).trans hsub1
    have h3 : (riemannZeta (2 + T * I) - 1).re = (riemannZeta (2 + T * I)).re - 1 := by simp
    rw [h3] at h2
    linarith [(abs_le.mp h2).1]
  have hthird := one_third_lt_two_sub_pi_sq_div_six
  have hg2 : symZeta T 2 = (((riemannZeta ((2:ℂ) + T * I)).re : ℝ) : ℂ) := by
    have h := symZeta_ofReal (T := T) 2 (by push_cast; exact hne2)
    push_cast at h ⊢
    exact h
  have hg2ne : symZeta T 2 ≠ 0 := by
    rw [hg2]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  set u : ℂ := (symZeta T 2)⁻¹ with hu
  have hu0 : u ≠ 0 := inv_ne_zero hg2ne
  have hnu : ‖u‖ ≤ 3 := by
    rw [hu, norm_inv, inv_le_comm₀ (by positivity) (by norm_num)]
    rw [hg2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  set G : ℂ → ℂ := fun w => symZeta T (2 + κ * w) * u with hG
  have hGanalytic : ∀ w : ℂ, ‖w‖ ≤ 1.05 → AnalyticAt ℂ G w := by
    intro w hw
    have hκw : ‖κ * w‖ ≤ 2 := by
      rw [norm_mul, hnormκ]; nlinarith [norm_nonneg w]
    obtain ⟨h1, h2⟩ := ne_one_of_im_large (z := κ * w) hT hκw
    have hs : AnalyticAt ℂ (symZeta T) (2 + κ * w) := by
      apply symZeta_analyticAt
      · rw [show (2:ℂ) + κ * w + T * I = κ * w + 2 + T * I by ring]; exact h1
      · rw [show (2:ℂ) + κ * w - T * I = κ * w + 2 - T * I by ring]; exact h2
    exact ((hs.comp_of_eq (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 2 + κ * w) w) rfl).mul
      analyticAt_const)
  have hG0 : G 0 = 1 := by
    simp only [hG, mul_zero, add_zero, hu]
    exact mul_inv_cancel₀ hg2ne
  have hball : AnalyticOnNhd ℂ G (Metric.ball 0 1.05) := by
    intro w hw
    rw [Metric.mem_ball, _root_.dist_zero_right] at hw
    exact hGanalytic w hw.le
  -- growth bound on ‖w‖ ≤ R
  set B : ℝ := 3 * C * (T + 5) ^ A' with hB
  have hBpos : 0 < B := by positivity
  have hκre : κ.re = 1.9 := by rw [hκ]; norm_num [Complex.ofReal_re]
  have hκim : κ.im = 0 := by rw [hκ]; simp
  have hfz : ∀ w : ℂ, ‖w‖ ≤ R → ‖G w‖ ≤ B := by
    intro w hw
    have hwre := abs_le.mp ((Complex.abs_re_le_norm w).trans hw)
    have hwim := abs_le.mp ((Complex.abs_im_le_norm w).trans hw)
    rw [hR] at hwre hwim
    have hκwre : (κ * w).re = 1.9 * w.re := by
      rw [Complex.mul_re, hκre, hκim]; ring
    have hκwim : (κ * w).im = 1.9 * w.im := by
      rw [Complex.mul_im, hκre, hκim]; ring
    have hzeta : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
        ‖riemannZeta (2 + κ * w + ε * T * I)‖ ≤ C * (T + 5) ^ A' := by
      intro ε hε
      set s : ℂ := 2 + κ * w + ε * T * I with hs
      have hsre : s.re = 2 + 1.9 * w.re := by
        rw [hs]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.mul_im, hκre, hκim]
        ring
      have hsim : s.im = 1.9 * w.im + ε * T := by
        rw [hs]
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.im_ofNat, Complex.mul_re, hκre, hκim]
        ring
      have hεT : T - 1.71 ≤ |1.9 * w.im + ε * T| := by
        rcases hε with rfl | rfl
        · rw [abs_of_pos (by nlinarith)]; nlinarith
        · rw [abs_of_neg (by nlinarith)]; nlinarith
      have h1 : (0.15:ℝ) ≤ s.re := by rw [hsre]; nlinarith
      have h2 : 1 ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        have : |(s - 1).im| ≤ ‖s - 1‖ := this
        have him : (s - 1).im = s.im := by simp
        rw [him, hsim] at this
        linarith [hεT.trans this]
      have h3 := hgrowth s h1 h2
      have hbase1 : (1:ℝ) ≤ |s.im| + 3 := by linarith [abs_nonneg s.im]
      have hA'A : (|s.im| + 3) ^ A ≤ (|s.im| + 3) ^ A' :=
        Real.rpow_le_rpow_of_exponent_le hbase1 (le_max_left _ _)
      have hbase : |s.im| + 3 ≤ T + 5 := by
        rw [hsim]
        have h4 := abs_add_le (1.9 * w.im) (ε * T)
        have h5 : |1.9 * w.im| ≤ 1.71 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1.9)]
          have : |w.im| ≤ 0.9 := abs_le.mpr ⟨hwim.1, hwim.2⟩
          nlinarith
        have h6 : |ε * T| = T := by
          rcases hε with rfl | rfl <;> rw [abs_mul] <;>
            simp [abs_of_pos (by linarith : (0:ℝ) < T)]
        linarith
      have hmono : (|s.im| + 3) ^ A' ≤ (T + 5) ^ A' :=
        Real.rpow_le_rpow (by positivity) hbase hA'0
      calc ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A := h3
        _ ≤ C * (T + 5) ^ A' := by
            exact mul_le_mul_of_nonneg_left (hA'A.trans hmono) hC.le
    have hgb : ‖symZeta T (2 + κ * w)‖ ≤ C * (T + 5) ^ A' := by
      have e1 : (2:ℂ) + κ * w + (1:ℝ) * T * I = 2 + κ * w + T * I := by push_cast; ring
      have e2 : (2:ℂ) + κ * w + (-1:ℝ) * T * I = 2 + κ * w - T * I := by push_cast; ring
      have ha := hzeta 1 (Or.inl rfl)
      have hb := hzeta (-1) (Or.inr rfl)
      rw [e1] at ha
      rw [e2] at hb
      unfold symZeta
      calc ‖(riemannZeta (2 + κ * w + T * I) + riemannZeta (2 + κ * w - T * I)) / 2‖
          = ‖riemannZeta (2 + κ * w + T * I) + riemannZeta (2 + κ * w - T * I)‖ / 2 := by
            rw [norm_div]; norm_num
        _ ≤ (‖riemannZeta (2 + κ * w + T * I)‖ + ‖riemannZeta (2 + κ * w - T * I)‖) / 2 := by
            gcongr
            exact norm_add_le _ _
        _ ≤ C * (T + 5) ^ A' := by linarith
    calc ‖G w‖ = ‖symZeta T (2 + κ * w)‖ * ‖u‖ := by rw [hG]; exact norm_mul _ _
      _ ≤ (C * (T + 5) ^ A') * 3 := by
          apply mul_le_mul hgb hnu (norm_nonneg _) (by positivity)
      _ ≤ B := by
          rw [hB]
          nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ T + 5) A']
  have hfAnalytic : AnalyticOnNhd ℂ G (Metric.closedBall (0:ℂ) R) := by
    intro w hw
    rw [Metric.mem_closedBall, _root_.dist_zero_right] at hw
    exact hGanalytic w (by rw [hR] at hw; linarith)
  obtain ⟨hfin, hZ⟩ := disk_zero_order_bound (r := r) (R := R)
    (by norm_num [hr]) (by norm_num [hr, hR]) hfAnalytic hG0 hfz
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have horder : ∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt G ρ := by
    intro ρ hρ
    rw [hZdef, Set.Finite.mem_toFinset] at hρ
    obtain ⟨hρr, hρ0⟩ := hρ
    have hρr' : ‖ρ‖ ≤ r := hρr
    have han : AnalyticAt ℂ G ρ := hGanalytic ρ (by rw [hr] at hρr'; linarith)
    have hne0 : analyticOrderAt G ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr hρ0
    have hnetop : analyticOrderAt G ρ ≠ ⊤ := by
      refine hball.analyticOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected
        (x := 0) ?_ ?_ ?_
      · rw [Metric.mem_ball, _root_.dist_zero_right]; simp; norm_num
      · rw [Metric.mem_ball, _root_.dist_zero_right]; rw [hr] at hρr'; linarith
      · rw [(hGanalytic 0 (by norm_num)).analyticOrderAt_eq_zero.mpr
          (by rw [hG0]; exact one_ne_zero)]
        exact ENat.zero_ne_top
    unfold analyticOrderNatAt
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
    rw [← hn] at hne0 ⊢
    simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
    omega
  -- the real zeros inject into Z
  set φ : ℝ → ℂ := fun σ => ((σ - 2 : ℝ) : ℂ) / κ with hφ
  have hφinj : Set.InjOn φ (reZeroSet T) := by
    intro a _ b _ h
    simp only [hφ] at h
    have h' : ((a - 2 : ℝ) : ℂ) = ((b - 2 : ℝ) : ℂ) := by
      have := congrArg (fun z => z * κ) h
      simpa [div_mul_cancel₀ _ hκ0] using this
    have := Complex.ofReal_inj.mp h'
    linarith
  have hmem : ∀ σ ∈ reZeroSet T, φ σ ∈ diskZeros r G := by
    rintro σ ⟨hσI, hσ0⟩
    have hσ1 : (1/2:ℝ) ≤ σ := hσI.1
    have hσ2 : σ ≤ 2 := hσI.2
    constructor
    · show ‖((σ - 2 : ℝ) : ℂ) / κ‖ ≤ r
      rw [norm_div, hnormκ, Complex.norm_real, Real.norm_eq_abs, hr]
      rw [abs_of_nonpos (by linarith)]
      rw [div_le_iff₀ (by norm_num)]
      linarith
    · show G (φ σ) = 0
      have hfix : (2:ℂ) + κ * φ σ = (σ:ℂ) := by
        simp only [hφ]
        field_simp
        push_cast
        ring
      have hne1 : (σ:ℂ) + T * I ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      simp only [hG, hfix]
      rw [symZeta_ofReal σ hne1, hσ0]
      simp
  have himg : φ '' (reZeroSet T) ⊆ (↑Z : Set ℂ) := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [hZdef]
    simp only [Set.Finite.coe_toFinset]
    exact hmem σ hσ
  have hfinRe : (reZeroSet T).Finite :=
    Set.Finite.of_finite_image (Z.finite_toSet.subset himg) hφinj
  refine ⟨hfinRe, ?_⟩
  have hcard : ((reZeroSet T).ncard : ℝ) ≤ (Z.card : ℝ) := by
    have h1 : (reZeroSet T).ncard = (φ '' reZeroSet T).ncard :=
      (hφinj.ncard_image).symm
    have h2 : (φ '' reZeroSet T).ncard ≤ (↑Z : Set ℂ).ncard :=
      Set.ncard_le_ncard himg Z.finite_toSet
    rw [Set.ncard_coe_finset] at h2
    exact_mod_cast h1 ▸ h2
  have hsum : (Z.card : ℝ) ≤ ((∑ ρ ∈ Z, analyticOrderNatAt G ρ : ℕ) : ℝ) := by
    have h := (Finset.card_eq_sum_ones Z).le.trans (Finset.sum_le_sum horder)
    exact_mod_cast h
  calc ((reZeroSet T).ncard : ℝ) ≤ (Z.card : ℝ) := hcard
    _ ≤ _ := hsum
    _ ≤ Real.log B / Real.log (R / r) := by exact_mod_cast hZ
    _ = _ := by rw [hB, hA', hR, hr]

lemma reZeroSet_card_le_linear_growth
    (hgrowth : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ (20 / 3 : ℝ) * (|s.im| + 3))
    (T : ℝ) (hT : 4 ≤ T) :
    (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤
      9 * Real.log (T + 5) + 27 := by
  have hg : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ (20 / 3 : ℝ) * (|s.im| + 3) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using hgrowth
  obtain ⟨hfin, hc⟩ := reZeroSet_card_raw (by norm_num : (0 : ℝ) < 20 / 3) hg T hT
  refine ⟨hfin, hc.trans ?_⟩
  norm_num [Real.rpow_one] at hc ⊢
  have hlog : (1 / 9 : ℝ) ≤ Real.log ((9 : ℝ) / 8) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 9 / 8)
    norm_num at h ⊢
    exact h
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have h20 : Real.log (20 : ℝ) ≤ 3 :=
    (Real.log_le_iff_le_exp (by norm_num)).2 (by linarith)
  have hTp : 0 < T + 5 := by linarith
  have hn : 0 ≤ Real.log (20 * (T + 5)) := Real.log_nonneg (by linarith)
  have hnum : Real.log (20 * (T + 5)) =
      Real.log 20 + Real.log (T + 5) := by
    exact Real.log_mul (by norm_num) hTp.ne'
  rw [hnum]
  have hn' : 0 ≤ Real.log 20 + Real.log (T + 5) := by
    rwa [Real.log_mul (by norm_num) hTp.ne'] at hn
  calc (Real.log 20 + Real.log (T + 5)) / Real.log (9 / 8)
      ≤ (Real.log 20 + Real.log (T + 5)) / (1 / 9) :=
        div_le_div_of_nonneg_left hn' (by norm_num) hlog
    _ ≤ 9 * Real.log (T + 5) + 27 := by linarith

lemma backlund_horizontal_raw_bound {A C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ C * (|s.im| + 3) ^ A)
    (T : ℝ) (hT : 4 ≤ T)
    (hnz : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0) :
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤
      Real.pi * (Real.log (3 * C * (T + 5) ^ max A 0) /
        Real.log ((0.9 : ℝ) / 0.8) + 1) := by
  obtain ⟨hfin, hc⟩ := reZeroSet_card_raw hC hgrowth T hT
  have hh := backlund_horizontal_card_bound (by linarith : T ≠ 0) hnz hfin.toFinset
    (by intro σ hσ hz; exact hfin.mem_toFinset.mpr ⟨hσ, hz⟩)
  rw [← Set.ncard_eq_toFinset_card (reZeroSet T) hfin] at hh
  exact hh.trans (by gcongr)

lemma backlund_horizontal_numerical_bound
    (hgrowth : ∀ s : ℂ, (0.15 : ℝ) ≤ s.re → 1 ≤ ‖s - 1‖ →
      ‖riemannZeta s‖ ≤ (20 / 3 : ℝ) * (|s.im| + 3))
    (T : ℝ) (hT : 4 ≤ T)
    (hnz : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0) :
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤
      Real.pi * (9 * Real.log (T + 5) + 28) := by
  obtain ⟨hfin, hc⟩ := reZeroSet_card_le_linear_growth hgrowth T hT
  have hh := backlund_horizontal_card_bound (by linarith : T ≠ 0) hnz hfin.toFinset
    (by intro σ hσ hz; exact hfin.mem_toFinset.mpr ⟨hσ, hz⟩)
  rw [← Set.ncard_eq_toFinset_card (reZeroSet T) hfin] at hh
  have h1 : ((reZeroSet T).ncard : ℝ) + 1 ≤ 9 * Real.log (T + 5) + 28 := by linarith
  exact hh.trans (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le)

end DusartSmoothing.RvM


