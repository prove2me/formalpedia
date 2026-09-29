-- Prove2me | Definitions.Def_CK_CKLaneA3W_ExactPoly
-- name    : CK_CKLaneA3W_ExactPoly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:32:53.462458+00:00
-- url     : https://prove2.me/theorems/5b7b6458-360f-4623-9f92-955d06d1ee80
-- title:
--   Courtade–Kumar proof module `CKLaneA3W.ExactPoly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3W.ExactPoly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3W.ExactPoly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3W.ExactPoly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3W/ExactPoly.lean)

import Definitions.Def_CK_CKLaneA3W_SeriesTM2

/-!
# CKLaneA3W.ExactPoly — exact polynomial constructions (divided-difference polynomial), divt
-/

namespace CKLaneA3W

open Finset

theorem good_divt {f : ℝ → ℝ → ℝ} {d : TMd} (h : Good f d) (hz : zeroPrefix d.P 1 = true) (hn : 1 ≤ d.n) :
    Good (fun t ρ => f t ρ / t) ⟨TPoly.drop d.P 1, d.r, d.n - 1⟩ := by
  refine ⟨?_, h.2⟩
  intro t ρ hd
  have ht := hd.1
  have h1 := h.1 t ρ hd
  have he := zeroPrefix_eval t (ρ - 1 / 2) (Real.log 2) d.P 1 hz
  unfold ev at h1 ⊢
  rw [he, pow_one] at h1
  have : f t ρ / t - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.drop d.P 1) =
      (f t ρ - t * TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.drop d.P 1)) / t := by field_simp
  show |f t ρ / t - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.drop d.P 1)| ≤ (d.r : ℝ) * t ^ (d.n - 1)
  rw [this, abs_div, abs_of_pos ht, div_le_iff₀ ht]
  calc _ ≤ (d.r : ℝ) * t ^ d.n := h1
    _ = (d.r : ℝ) * t ^ (d.n - 1) * t := by
        rw [mul_assoc, ← pow_succ]; congr 2; omega

/-- `s = 1 - ρ = 1/2 - σ` -/
def sP : SPoly := [(0, [(0, 1 / 2)]), (1, [(0, -1)])]

theorem sP_eval (σ L : ℝ) : SPoly.eval σ L sP = 1 / 2 - σ := by
  simp [sP, SPoly.eval_cons, SPoly.eval_nil, LPoly.eval_cons, LPoly.eval_nil]; ring

noncomputable def sPow (m : ℕ) : SPoly := Nat.rec (motive := fun _ => SPoly) [(0, [(0, 1)])]
  (fun _ ih => SPoly.mul sP ih) m

theorem sPow_eval (σ L : ℝ) (hL : L ≠ 0) (m : ℕ) : SPoly.eval σ L (sPow m) = (1 / 2 - σ) ^ m := by
  induction m with
  | zero => simp [sPow, SPoly.eval_cons, SPoly.eval_nil, LPoly.eval_cons, LPoly.eval_nil]
  | succ m ih =>
    show SPoly.eval σ L (SPoly.mul sP (sPow m)) = _
    rw [SPoly.eval_mul σ L hL, sP_eval, ih, pow_succ]; ring

noncomputable def geoS (m : ℕ) : SPoly := Nat.rec (motive := fun _ => SPoly) []
  (fun k ih => SPoly.add ih (sPow k)) m

theorem geoS_eval (σ L : ℝ) (hL : L ≠ 0) (m : ℕ) :
    SPoly.eval σ L (geoS m) = ∑ j ∈ range m, (1 / 2 - σ) ^ j := by
  induction m with
  | zero => simp [geoS, SPoly.eval_nil]
  | succ m ih =>
    show SPoly.eval σ L (SPoly.add (geoS m) (sPow m)) = _
    rw [SPoly.eval_add σ L hL, ih, sPow_eval σ L hL, sum_range_succ]

noncomputable def monoT (m : ℕ) (s : SPoly) : TPoly := Nat.rec (motive := fun _ => TPoly) [s]
  (fun _ ih => [] :: ih) m

theorem monoT_eval (t σ L : ℝ) (m : ℕ) (s : SPoly) :
    TPoly.eval t σ L (monoT m s) = t ^ m * SPoly.eval σ L s := by
  induction m with
  | zero => simp [monoT, TPoly.eval_cons, TPoly.eval_nil]
  | succ m ih =>
    show TPoly.eval t σ L ([] :: monoT m s) = _
    rw [TPoly.eval_cons, SPoly.eval_nil, ih, pow_succ]; ring

noncomputable def ddPoly (K : ℕ) : TPoly := Nat.rec (motive := fun _ => TPoly) []
  (fun k ih => TPoly.add ih (monoT (2 * k) (SPoly.scale ((4 : ℚ) ^ k / (2 * k + 1)) (geoS (2 * k + 1))))) K

theorem ddPoly_eval (t σ L : ℝ) (hL : L ≠ 0) (K : ℕ) :
    TPoly.eval t σ L (ddPoly K) =
      ∑ k ∈ range K, t ^ (2 * k) * ((4 : ℝ) ^ k / (2 * k + 1)) * ∑ j ∈ range (2 * k + 1), (1 / 2 - σ) ^ j := by
  induction K with
  | zero => simp [ddPoly, TPoly.eval_nil]
  | succ K ih =>
    show TPoly.eval t σ L (TPoly.add (ddPoly K)
      (monoT (2 * K) (SPoly.scale ((4 : ℚ) ^ K / (2 * K + 1)) (geoS (2 * K + 1))))) = _
    rw [TPoly.eval_add t σ L hL, ih, monoT_eval, SPoly.eval_scale, geoS_eval σ L hL,
      Finset.sum_range_succ _ K]
    push_cast; ring

theorem dd_poly_identity (t ρ : ℝ) (k : ℕ) :
    ∑ i ∈ range (2 * k + 1), (2 * t) ^ i * (2 * ((1 - ρ) * t)) ^ (2 * k - i) =
      t ^ (2 * k) * (4 : ℝ) ^ k * ∑ j ∈ range (2 * k + 1), (1 - ρ) ^ j := by
  have h1 : ∀ i ∈ range (2 * k + 1), (2 * t) ^ i * (2 * ((1 - ρ) * t)) ^ (2 * k - i) =
      t ^ (2 * k) * (4 : ℝ) ^ k * (1 - ρ) ^ (2 * k - i) := by
    intro i hi
    rw [mem_range] at hi
    have hle : i ≤ 2 * k := by omega
    have e1 : (2 * t) ^ i * (2 * ((1 - ρ) * t)) ^ (2 * k - i) =
        (2 : ℝ) ^ (i + (2 * k - i)) * t ^ (i + (2 * k - i)) * (1 - ρ) ^ (2 * k - i) := by
      rw [mul_pow, mul_pow, mul_pow, pow_add, pow_add]; ring
    rw [e1, Nat.add_sub_cancel' hle]
    rw [show (2 : ℝ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]
    ring
  rw [sum_congr rfl h1, ← mul_sum]
  congr 1
  exact sum_range_reflect (fun j => (1 - ρ) ^ j) (2 * k + 1)

theorem ddPoly_ev (K : ℕ) (t ρ : ℝ) :
    ev (ddPoly K) t ρ = ∑ k ∈ range K, (1 / (2 * (k : ℝ) + 1)) *
      ∑ i ∈ range (2 * k + 1), (2 * t) ^ i * (2 * ((1 - ρ) * t)) ^ (2 * k - i) := by
  unfold ev
  have hL : Real.log 2 ≠ 0 := by positivity
  rw [ddPoly_eval t (ρ - 1 / 2) (Real.log 2) hL K]
  apply sum_congr rfl
  intro k _
  rw [dd_poly_identity]
  have : (1 / 2 - (ρ - 1 / 2)) = 1 - ρ := by ring
  rw [this]
  have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem good_dd (K n : ℕ) (hK : n ≤ 2 * K) (r' : ℚ)
    (hr' : bsum (ldrop (entryBounds (ddPoly K)) n) + 4 ^ K * Tq ^ (2 * K - n) / (1 - 4 * Tq ^ 2) ≤ r') :
    Good (fun t ρ => (atanhR (2 * ((1 - ρ) * t)) - atanhR (2 * t)) / (2 * ((1 - ρ) * t) - 2 * t))
      ⟨TPoly.take (ddPoly K) n, r', n⟩ := by
  have hT : (Tq : ℚ) = 7 / 50 := rfl
  have hden : (0 : ℚ) < 1 - 4 * Tq ^ 2 := by rw [hT]; norm_num
  have hpolyE : Encl (fun t ρ => ev (ddPoly K) t ρ) (ddPoly K) 0 n := Encl.exact n (fun _ _ _ => rfl)
  have htr := Encl.trunc hpolyE (entryBounds_spec _) (le_refl n) (le_refl _) (le_refl _)
  simp only [Nat.sub_self, pow_zero, mul_one, add_zero] at htr
  refine ⟨?_, ?_⟩
  · intro t ρ hd
    have ht0 := hd.1.le
    have h1 := htr t ρ hd
    have hTr : (Tq : ℝ) = 7 / 50 := by norm_num [Tq]
    have hx : |2 * t| ≤ 2 * t := by rw [abs_of_nonneg (by linarith)]
    have hy : |2 * ((1 - ρ) * t)| ≤ 2 * t := by
      have h3 := hd.2.2.1; have h4 := hd.2.2.2
      rw [abs_of_nonneg (by nlinarith)]; nlinarith
    have hX : 2 * t < 1 := by linarith [hd.2.1]
    have hxy : 2 * t ≠ 2 * ((1 - ρ) * t) := by
      have h3 := hd.2.2.1; have h1' := hd.1; nlinarith
    have hser := dd_atanh_series hxy hx hy hX K
    rw [← ddPoly_ev K t ρ] at hser
    have hden' : (0 : ℝ) < 1 - 4 * (Tq : ℝ) ^ 2 := by rw [hTr]; norm_num
    have ht2 : (2 * t) ^ 2 ≤ 4 * (Tq : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ ht0 hd.2.1 2; nlinarith
    have hpow : (2 * t) ^ (2 * K) ≤ (4 : ℝ) ^ K * (Tq : ℝ) ^ (2 * K - n) * t ^ n := by
      have e : (2 * t) ^ (2 * K) = (4 : ℝ) ^ K * t ^ (2 * K) := by
        rw [mul_pow, pow_mul]; norm_num
      rw [e, mul_assoc]
      exact mul_le_mul_of_nonneg_left (pow_le_T_pow ht0 hd.2.1 hK) (by positivity)
    have hA : |(atanhR (2 * ((1 - ρ) * t)) - atanhR (2 * t)) / (2 * ((1 - ρ) * t) - 2 * t) - ev (ddPoly K) t ρ| ≤
        ((4 : ℝ) ^ K * (Tq : ℝ) ^ (2 * K - n) / (1 - 4 * (Tq : ℝ) ^ 2)) * t ^ n := by
      refine hser.trans ?_
      rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 1 - (2 * t) ^ 2)]
      calc (2 * t) ^ (2 * K) ≤ (4 : ℝ) ^ K * (Tq : ℝ) ^ (2 * K - n) * t ^ n := hpow
        _ = ((4 : ℝ) ^ K * (Tq : ℝ) ^ (2 * K - n) / (1 - 4 * (Tq : ℝ) ^ 2)) * t ^ n *
              (1 - 4 * (Tq : ℝ) ^ 2) := by field_simp
        _ ≤ ((4 : ℝ) ^ K * (Tq : ℝ) ^ (2 * K - n) / (1 - 4 * (Tq : ℝ) ^ 2)) * t ^ n * (1 - (2 * t) ^ 2) := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            have : (0 : ℝ) ≤ (Tq : ℝ) ^ (2 * K - n) := pow_nonneg Tq_pos.le _
            positivity
    have hr'' : ((bsum (ldrop (entryBounds (ddPoly K)) n) : ℚ) : ℝ) +
        (4 : ℝ) ^ K * (Tq : ℝ) ^ (2 * K - n) / (1 - 4 * (Tq : ℝ) ^ 2) ≤ r' := by exact_mod_cast hr'
    show |_ - ev (TPoly.take (ddPoly K) n) t ρ| ≤ (r' : ℝ) * t ^ n
    calc _ ≤ |(atanhR (2 * ((1 - ρ) * t)) - atanhR (2 * t)) / (2 * ((1 - ρ) * t) - 2 * t) - ev (ddPoly K) t ρ| +
          |ev (ddPoly K) t ρ - ev (TPoly.take (ddPoly K) n) t ρ| := abs_sub_le _ _ _
      _ ≤ ((4 : ℝ) ^ K * (Tq : ℝ) ^ (2 * K - n) / (1 - 4 * (Tq : ℝ) ^ 2)) * t ^ n +
          ((bsum (ldrop (entryBounds (ddPoly K)) n) : ℚ) : ℝ) * t ^ n := add_le_add hA h1
      _ = (((bsum (ldrop (entryBounds (ddPoly K)) n) : ℚ) : ℝ) +
          (4 : ℝ) ^ K * (Tq : ℝ) ^ (2 * K - n) / (1 - 4 * (Tq : ℝ) ^ 2)) * t ^ n := by ring
      _ ≤ (r' : ℝ) * t ^ n := mul_le_mul_of_nonneg_right hr'' (pow_nonneg ht0 _)
  · refine le_trans ?_ hr'
    have := bsum_nonneg _ (ldrop_nonneg _ (entryBounds_spec (ddPoly K)).nonneg n)
    have : (0 : ℚ) ≤ Tq ^ (2 * K - n) := pow_nonneg Tq_nonneg _
    have : 0 ≤ 4 ^ K * Tq ^ (2 * K - n) / (1 - 4 * Tq ^ 2) := by positivity
    linarith

end CKLaneA3W


