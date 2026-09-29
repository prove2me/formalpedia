-- Prove2me | Definitions.Def_CK_CKLaneA3V_SeriesTM2
-- name    : CK_CKLaneA3V_SeriesTM2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:30:55.534815+00:00
-- url     : https://prove2.me/theorems/1f711a85-ecf1-47b1-9fdd-00e7183db941
-- title:
--   Courtade–Kumar proof module `CKLaneA3V.SeriesTM2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3V.SeriesTM2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3V.SeriesTM2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3V.SeriesTM2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3V/SeriesTM2.lean)

import Definitions.Def_CK_CKLaneA3V_SeriesTM

/-!
# CKLaneA3V.SeriesTM2 — atanh/x, log(1-z), reciprocal, exact polynomials, divided difference
-/

namespace CKLaneA3V

open Finset

theorem good_atanhdiv {x : ℝ → ℝ → ℝ} {X Y : TMd} (hx : Good x X) (K : ℕ)
    (hz : zeroPrefix X.P 1 = true) (h1 : 1 ≤ X.n) (hx0 : ∀ t ρ, Dom t ρ → x t ρ ≠ 0)
    (hY : Good (fun t ρ => hornerR (atanhCoeffs K) (x t ρ * x t ρ)) Y)
    (κ : ℚ) (hκ : bsum (ldrop (entryBounds X.P) 1) + X.r * Tq ^ (X.n - 1) ≤ κ) (hκT : κ * Tq < 1)
    (hK : Y.n ≤ 2 * K) (r' : ℚ)
    (hr' : Y.r + κ ^ (2 * K) * Tq ^ (2 * K - Y.n) / (1 - κ * Tq) ≤ r') :
    Good (fun t ρ => atanhR (x t ρ) / x t ρ) ⟨Y.P, r', Y.n⟩ := by
  have hY0 := hY.2
  have hκq : 0 ≤ κ := le_trans (add_nonneg (bsum_nonneg _ (ldrop_nonneg _ (entryBounds_spec _).nonneg _))
      (mul_nonneg hx.2 (pow_nonneg Tq_nonneg _))) hκ
  refine ⟨?_, ?_⟩
  · intro t ρ hd
    have ht0 := hd.1.le
    have hxb := hx.abs_le' hz h1 hκ hd
    rw [pow_one] at hxb
    have hκ0 : (0 : ℝ) ≤ κ := by exact_mod_cast hκq
    have hκT' : (κ : ℝ) * (Tq : ℝ) < 1 := by exact_mod_cast hκT
    have hxT : |x t ρ| ≤ (κ : ℝ) * Tq := hxb.trans (mul_le_mul_of_nonneg_left hd.2.1 hκ0)
    have hx1 : |x t ρ| < 1 := lt_of_le_of_lt hxT hκT'
    have hser := atanh_div_series hx1 (hx0 t ρ hd) K
    have hYe := hY.1 t ρ hd
    simp only at hYe
    rw [atanhdiv_horner] at hYe
    have hden' : 1 - (κ : ℝ) * Tq ≤ 1 - |x t ρ| := by linarith
    have hden0 : (1 - (κ : ℝ) * Tq) ≠ 0 := ne_of_gt (by linarith)
    have hpow : |x t ρ| ^ (2 * K) ≤ ((κ : ℝ) ^ (2 * K) * (Tq : ℝ) ^ (2 * K - Y.n)) * t ^ Y.n := by
      calc |x t ρ| ^ (2 * K) ≤ ((κ : ℝ) * t) ^ (2 * K) := pow_le_pow_left₀ (abs_nonneg _) hxb _
        _ = (κ : ℝ) ^ (2 * K) * t ^ (2 * K) := by rw [mul_pow]
        _ ≤ (κ : ℝ) ^ (2 * K) * ((Tq : ℝ) ^ (2 * K - Y.n) * t ^ Y.n) :=
            mul_le_mul_of_nonneg_left (pow_le_T_pow ht0 hd.2.1 hK) (pow_nonneg hκ0 _)
        _ = _ := by ring
    have hA : |atanhR (x t ρ) / x t ρ - ∑ k ∈ range K, x t ρ ^ (2 * k) / (2 * (k : ℝ) + 1)| ≤
        ((κ : ℝ) ^ (2 * K) * (Tq : ℝ) ^ (2 * K - Y.n) / (1 - κ * Tq)) * t ^ Y.n := by
      refine hser.trans ?_
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - |x t ρ|)]
      calc |x t ρ| ^ (2 * K) ≤ ((κ : ℝ) ^ (2 * K) * (Tq : ℝ) ^ (2 * K - Y.n)) * t ^ Y.n := hpow
        _ = ((κ : ℝ) ^ (2 * K) * (Tq : ℝ) ^ (2 * K - Y.n) / (1 - κ * Tq)) * t ^ Y.n *
              (1 - κ * Tq) := by field_simp
        _ ≤ ((κ : ℝ) ^ (2 * K) * (Tq : ℝ) ^ (2 * K - Y.n) / (1 - κ * Tq)) * t ^ Y.n *
              (1 - |x t ρ|) := by
            apply mul_le_mul_of_nonneg_left hden'
            have : (0 : ℝ) < 1 - κ * Tq := by linarith
            have : (0 : ℝ) ≤ (Tq : ℝ) ^ (2 * K - Y.n) := pow_nonneg Tq_pos.le _
            positivity
    have hr'' : (Y.r : ℝ) + (κ : ℝ) ^ (2 * K) * (Tq : ℝ) ^ (2 * K - Y.n) / (1 - κ * Tq) ≤ r' := by
      exact_mod_cast hr'
    show |atanhR (x t ρ) / x t ρ - ev Y.P t ρ| ≤ (r' : ℝ) * t ^ Y.n
    calc |atanhR (x t ρ) / x t ρ - ev Y.P t ρ|
        ≤ |atanhR (x t ρ) / x t ρ - ∑ k ∈ range K, x t ρ ^ (2 * k) / (2 * (k : ℝ) + 1)| +
          |∑ k ∈ range K, x t ρ ^ (2 * k) / (2 * (k : ℝ) + 1) - ev Y.P t ρ| := abs_sub_le _ _ _
      _ ≤ ((κ : ℝ) ^ (2 * K) * (Tq : ℝ) ^ (2 * K - Y.n) / (1 - κ * Tq)) * t ^ Y.n +
          (Y.r : ℝ) * t ^ Y.n := add_le_add hA hYe
      _ = ((Y.r : ℝ) + (κ : ℝ) ^ (2 * K) * (Tq : ℝ) ^ (2 * K - Y.n) / (1 - κ * Tq)) * t ^ Y.n := by ring
      _ ≤ (r' : ℝ) * t ^ Y.n := mul_le_mul_of_nonneg_right hr'' (pow_nonneg ht0 _)
  · refine le_trans ?_ hr'
    have : 0 < 1 - κ * Tq := by linarith
    have : (0 : ℚ) ≤ Tq ^ (2 * K - Y.n) := pow_nonneg Tq_nonneg _
    have : 0 ≤ κ ^ (2 * K) * Tq ^ (2 * K - Y.n) / (1 - κ * Tq) := by positivity
    linarith

theorem good_log1m {z : ℝ → ℝ → ℝ} {Z Y : TMd} (hz : Good z Z) (m : ℕ)
    (hzp : zeroPrefix Z.P 2 = true) (h2 : 2 ≤ Z.n)
    (hY : Good (fun t ρ => z t ρ * hornerR (logCoeffs m) (z t ρ)) Y)
    (κ : ℚ) (hκ : bsum (ldrop (entryBounds Z.P) 2) + Z.r * Tq ^ (Z.n - 2) ≤ κ) (hκT : κ * Tq ^ 2 < 1)
    (hK : Y.n ≤ 2 * m + 2) (r' : ℚ)
    (hr' : Y.r + κ ^ (m + 1) * Tq ^ (2 * m + 2 - Y.n) / (1 - κ * Tq ^ 2) ≤ r') :
    Good (fun t ρ => Real.log (1 - z t ρ)) ⟨TPoly.scale (-1) Y.P, r', Y.n⟩ := by
  have hY0 := hY.2
  have hκq : 0 ≤ κ := le_trans (add_nonneg (bsum_nonneg _ (ldrop_nonneg _ (entryBounds_spec _).nonneg _))
      (mul_nonneg hz.2 (pow_nonneg Tq_nonneg _))) hκ
  refine ⟨?_, ?_⟩
  · intro t ρ hd
    have ht0 := hd.1.le
    have hzb := hz.abs_le' hzp h2 hκ hd
    have hκ0 : (0 : ℝ) ≤ κ := by exact_mod_cast hκq
    have hκT' : (κ : ℝ) * (Tq : ℝ) ^ 2 < 1 := by exact_mod_cast hκT
    have ht2 : t ^ 2 ≤ (Tq : ℝ) ^ 2 := pow_le_pow_left₀ ht0 hd.2.1 2
    have hzT : |z t ρ| ≤ (κ : ℝ) * Tq ^ 2 := hzb.trans (mul_le_mul_of_nonneg_left ht2 hκ0)
    have hz1 : |z t ρ| < 1 := lt_of_le_of_lt hzT hκT'
    have hser := log1m_series hz1 m
    have hYe := hY.1 t ρ hd
    simp only at hYe
    rw [log_horner] at hYe
    have hden' : 1 - (κ : ℝ) * Tq ^ 2 ≤ 1 - |z t ρ| := by linarith
    have hden0 : (1 - (κ : ℝ) * Tq ^ 2) ≠ 0 := ne_of_gt (by linarith)
    have hpow : |z t ρ| ^ (m + 1) ≤ ((κ : ℝ) ^ (m + 1) * (Tq : ℝ) ^ (2 * m + 2 - Y.n)) * t ^ Y.n := by
      calc |z t ρ| ^ (m + 1) ≤ ((κ : ℝ) * t ^ 2) ^ (m + 1) := pow_le_pow_left₀ (abs_nonneg _) hzb _
        _ = (κ : ℝ) ^ (m + 1) * t ^ (2 * m + 2) := by rw [mul_pow, ← pow_mul]; ring_nf
        _ ≤ (κ : ℝ) ^ (m + 1) * ((Tq : ℝ) ^ (2 * m + 2 - Y.n) * t ^ Y.n) :=
            mul_le_mul_of_nonneg_left (pow_le_T_pow ht0 hd.2.1 hK) (pow_nonneg hκ0 _)
        _ = _ := by ring
    have hA : |Real.log (1 - z t ρ) + ∑ i ∈ range m, z t ρ ^ (i + 1) / ((i : ℝ) + 1)| ≤
        ((κ : ℝ) ^ (m + 1) * (Tq : ℝ) ^ (2 * m + 2 - Y.n) / (1 - κ * Tq ^ 2)) * t ^ Y.n := by
      refine hser.trans ?_
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - |z t ρ|)]
      calc |z t ρ| ^ (m + 1) ≤ ((κ : ℝ) ^ (m + 1) * (Tq : ℝ) ^ (2 * m + 2 - Y.n)) * t ^ Y.n := hpow
        _ = ((κ : ℝ) ^ (m + 1) * (Tq : ℝ) ^ (2 * m + 2 - Y.n) / (1 - κ * Tq ^ 2)) * t ^ Y.n *
              (1 - κ * Tq ^ 2) := by field_simp
        _ ≤ ((κ : ℝ) ^ (m + 1) * (Tq : ℝ) ^ (2 * m + 2 - Y.n) / (1 - κ * Tq ^ 2)) * t ^ Y.n *
              (1 - |z t ρ|) := by
            apply mul_le_mul_of_nonneg_left hden'
            have : (0 : ℝ) < 1 - κ * Tq ^ 2 := by linarith
            have : (0 : ℝ) ≤ (Tq : ℝ) ^ (2 * m + 2 - Y.n) := pow_nonneg Tq_pos.le _
            positivity
    have hr'' : (Y.r : ℝ) + (κ : ℝ) ^ (m + 1) * (Tq : ℝ) ^ (2 * m + 2 - Y.n) / (1 - κ * Tq ^ 2) ≤ r' := by
      exact_mod_cast hr'
    have hev : ev (TPoly.scale (-1) Y.P) t ρ = -(ev Y.P t ρ) := by
      unfold ev; rw [TPoly.eval_scale]; push_cast; ring
    show |Real.log (1 - z t ρ) - ev (TPoly.scale (-1) Y.P) t ρ| ≤ (r' : ℝ) * t ^ Y.n
    rw [hev, sub_neg_eq_add]
    calc |Real.log (1 - z t ρ) + ev Y.P t ρ|
        = |(Real.log (1 - z t ρ) + ∑ i ∈ range m, z t ρ ^ (i + 1) / ((i : ℝ) + 1)) -
            (∑ i ∈ range m, z t ρ ^ (i + 1) / ((i : ℝ) + 1) - ev Y.P t ρ)| := by ring_nf
      _ ≤ |Real.log (1 - z t ρ) + ∑ i ∈ range m, z t ρ ^ (i + 1) / ((i : ℝ) + 1)| +
          |∑ i ∈ range m, z t ρ ^ (i + 1) / ((i : ℝ) + 1) - ev Y.P t ρ| := abs_sub _ _
      _ ≤ ((κ : ℝ) ^ (m + 1) * (Tq : ℝ) ^ (2 * m + 2 - Y.n) / (1 - κ * Tq ^ 2)) * t ^ Y.n +
          (Y.r : ℝ) * t ^ Y.n := add_le_add hA hYe
      _ = ((Y.r : ℝ) + (κ : ℝ) ^ (m + 1) * (Tq : ℝ) ^ (2 * m + 2 - Y.n) / (1 - κ * Tq ^ 2)) * t ^ Y.n := by ring
      _ ≤ (r' : ℝ) * t ^ Y.n := mul_le_mul_of_nonneg_right hr'' (pow_nonneg ht0 _)
  · refine le_trans ?_ hr'
    have : 0 < 1 - κ * Tq ^ 2 := by linarith
    have : (0 : ℚ) ≤ Tq ^ (2 * m + 2 - Y.n) := pow_nonneg Tq_nonneg _
    have : 0 ≤ κ ^ (m + 1) * Tq ^ (2 * m + 2 - Y.n) / (1 - κ * Tq ^ 2) := by positivity
    linarith

/-! ## lower bounds and reciprocals -/

noncomputable def SPoly.lowB (s : SPoly) : ℚ :=
  @List.rec (ℕ × LPoly) (fun _ => ℚ) 0
    (fun m rest _ => if m.1 = 0 then (LPoly.intv m.2).1 - SPoly.absB rest else -SPoly.absB (m :: rest)) s

theorem SPoly.lowB_spec {σ L : ℝ} (hσ : |σ| ≤ 1 / 2) (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ))
    (s : SPoly) : (SPoly.lowB s : ℝ) ≤ SPoly.eval σ L s := by
  cases s with
  | nil => simp [SPoly.lowB, SPoly.eval_nil]
  | cons m rest =>
    show ((if m.1 = 0 then (LPoly.intv m.2).1 - SPoly.absB rest else -SPoly.absB (m :: rest) : ℚ) : ℝ) ≤ _
    split_ifs with hm
    · rw [SPoly.eval_cons, hm, pow_zero, one_mul]
      have ha := (LPoly.intv_spec h1 h2 m.2).1
      have hb := SPoly.absB_spec hσ h1 h2 rest
      have hb' := neg_abs_le (SPoly.eval σ L rest)
      push_cast
      linarith
    · have hb := SPoly.absB_spec hσ h1 h2 (m :: rest)
      have hb' := neg_abs_le (SPoly.eval σ L (m :: rest))
      push_cast
      linarith

noncomputable def TPoly.lowB (P : TPoly) : ℚ :=
  @List.rec SPoly (fun _ => ℚ) 0 (fun s rest _ => SPoly.lowB s - Tq * bsum (entryBounds rest)) P

theorem TPoly.lowB_spec {t σ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) (hσ : |σ| ≤ 1 / 2) (P : TPoly) :
    (TPoly.lowB P : ℝ) ≤ TPoly.eval t σ (Real.log 2) P := by
  cases P with
  | nil => simp [TPoly.lowB, TPoly.eval_nil]
  | cons s rest =>
    show ((SPoly.lowB s - Tq * bsum (entryBounds rest) : ℚ) : ℝ) ≤ _
    rw [TPoly.eval_cons]
    have h1 := SPoly.lowB_spec hσ log2_lo log2_hi s
    have h2 := (entryBounds_spec rest).eval_le ht0 ht hσ
    have h3 : -(t * |TPoly.eval t σ (Real.log 2) rest|) ≤ t * TPoly.eval t σ (Real.log 2) rest := by
      have := neg_abs_le (t * TPoly.eval t σ (Real.log 2) rest)
      rwa [abs_mul, abs_of_nonneg ht0] at this
    have h4 : t * |TPoly.eval t σ (Real.log 2) rest| ≤ (Tq : ℝ) * bsum (entryBounds rest) :=
      mul_le_mul ht h2 (abs_nonneg _) Tq_pos.le
    push_cast
    linarith

theorem Good.lower {p : ℝ → ℝ → ℝ} {D : TMd} (hp : Good p D) {t ρ : ℝ} (hd : Dom t ρ) :
    ((TPoly.lowB D.P - D.r * Tq ^ D.n : ℚ) : ℝ) ≤ p t ρ := by
  have h1 := hp.1 t ρ hd
  have h2 := TPoly.lowB_spec hd.1.le hd.2.1 hd.sigma D.P
  have h3 : t ^ D.n ≤ (Tq : ℝ) ^ D.n := pow_le_pow_left₀ hd.1.le hd.2.1 _
  have hr : (0 : ℝ) ≤ D.r := by exact_mod_cast hp.2
  unfold ev at h1
  have h4 := neg_abs_le (p t ρ - TPoly.eval t (ρ - 1 / 2) (Real.log 2) D.P)
  have h5 : (D.r : ℝ) * t ^ D.n ≤ D.r * (Tq : ℝ) ^ D.n := mul_le_mul_of_nonneg_left h3 hr
  push_cast
  linarith

noncomputable def allEmpty (P : TPoly) : Bool :=
  @List.rec SPoly (fun _ => Bool) true (fun s _ ih => s.isEmpty && ih) P

noncomputable def isOneT (P : TPoly) : Bool :=
  @List.rec SPoly (fun _ => Bool) false
    (fun s rest _ => decide (s = [(0, [(0, 1)])]) && allEmpty rest) P

theorem allEmpty_eval (t σ L : ℝ) (P : TPoly) (h : allEmpty P = true) : TPoly.eval t σ L P = 0 := by
  induction P with
  | nil => rfl
  | cons s rest ih =>
    have h' : s.isEmpty = true ∧ allEmpty rest = true := by
      have : allEmpty (s :: rest) = (s.isEmpty && allEmpty rest) := rfl
      rw [this] at h; simpa using h
    rw [TPoly.eval_cons, List.isEmpty_iff.mp h'.1, SPoly.eval_nil, ih h'.2]; ring

theorem isOneT_eval (t σ L : ℝ) (P : TPoly) (h : isOneT P = true) : TPoly.eval t σ L P = 1 := by
  cases P with
  | nil => exact absurd h (by simp [isOneT])
  | cons s rest =>
    have h' : decide (s = [(0, [(0, 1)])]) = true ∧ allEmpty rest = true := by
      have : isOneT (s :: rest) = (decide (s = [(0, [(0, 1)])]) && allEmpty rest) := rfl
      rw [this] at h; simpa using h
    have hs : s = [(0, [(0, 1)])] := by simpa using h'.1
    rw [TPoly.eval_cons, allEmpty_eval t σ L rest h'.2, hs]
    simp [SPoly.eval_cons, SPoly.eval_nil, LPoly.eval_cons, LPoly.eval_nil]

theorem good_exact {f : ℝ → ℝ → ℝ} (P : TPoly) (n : ℕ) (h : ∀ t ρ, Dom t ρ → f t ρ = ev P t ρ) :
    Good f ⟨P, 0, n⟩ := ⟨Encl.exact n h, le_refl _⟩

theorem good_evP (P : TPoly) (n : ℕ) : Good (fun t ρ => ev P t ρ) ⟨P, 0, n⟩ :=
  good_exact P n (fun _ _ _ => rfl)

theorem good_recip {p : ℝ → ℝ → ℝ} {D : TMd} (hp : Good p D) (Q : TPoly) (n : ℕ) (hn : n ≤ D.n)
    (hone : isOneT (TMd.mul D ⟨Q, 0, n⟩ 0 0 n).P = true)
    (pmin : ℚ) (hpmin : 0 < pmin) (hlow : pmin ≤ TPoly.lowB D.P - D.r * Tq ^ D.n)
    (r' : ℚ) (hr' : (TMd.mul D ⟨Q, 0, n⟩ 0 0 n).r / pmin ≤ r') :
    Good (fun t ρ => 1 / p t ρ) ⟨Q, r', n⟩ := by
  set E := TMd.mul D ⟨Q, 0, n⟩ 0 0 n with hE
  have hEg : Good (fun t ρ => p t ρ * ev Q t ρ) E :=
    TMd.mul_good hp (good_evP Q n) 0 0 n (zeroPrefix_zero _) (zeroPrefix_zero _) (Nat.zero_le _)
      (by simp) (by simpa using hn)
  have hEn : E.n = n := rfl
  refine ⟨?_, ?_⟩
  · intro t ρ hd
    have ht0 := hd.1.le
    have h1 := hEg.1 t ρ hd
    have hone' : ev E.P t ρ = 1 := isOneT_eval _ _ _ _ hone
    rw [hone', hEn] at h1
    have hlow' := hp.lower hd
    have hpm : (pmin : ℝ) ≤ p t ρ := le_trans (by exact_mod_cast hlow) hlow'
    have hpm0 : (0 : ℝ) < pmin := by exact_mod_cast hpmin
    have hp0 : 0 < p t ρ := lt_of_lt_of_le hpm0 hpm
    have hr'' : (E.r : ℝ) / pmin ≤ r' := by exact_mod_cast hr'
    show |1 / p t ρ - ev Q t ρ| ≤ (r' : ℝ) * t ^ n
    have hkey : 1 / p t ρ - ev Q t ρ = -(p t ρ * ev Q t ρ - 1) / p t ρ := by field_simp; ring
    rw [hkey, abs_div, abs_neg, abs_of_pos hp0, div_le_iff₀ hp0]
    have hEr : (0 : ℝ) ≤ E.r := by exact_mod_cast hEg.2
    calc |p t ρ * ev Q t ρ - 1| ≤ E.r * t ^ n := h1
      _ = ((E.r : ℝ) / pmin) * t ^ n * pmin := by field_simp
      _ ≤ (r' : ℝ) * t ^ n * p t ρ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hr'' (pow_nonneg ht0 _)) hpm hpm0.le
          have : (0 : ℝ) ≤ E.r / pmin := div_nonneg hEr hpm0.le
          have := le_trans this hr''
          positivity
  · refine le_trans ?_ hr'
    exact div_nonneg hEg.2 hpmin.le

end CKLaneA3V


