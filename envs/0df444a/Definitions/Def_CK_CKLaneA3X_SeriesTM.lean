-- Prove2me | Definitions.Def_CK_CKLaneA3X_SeriesTM
-- name    : CK_CKLaneA3X_SeriesTM
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:26:01.525976+00:00
-- url     : https://prove2.me/theorems/360dee49-c171-40da-9ed2-04916281f72a
-- title:
--   Courtade–Kumar proof module `CKLaneA3X.SeriesTM` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3X.SeriesTM` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3X.SeriesTM` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3X.SeriesTM (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/SeriesTM.lean)

import Definitions.Def_CK_CKLaneA3X_Series

/-!
# CKLaneA3X.SeriesTM — TM-level series, reciprocal and exact-polynomial helpers
-/

namespace CKLaneA3X

open Finset

theorem Good.of_eq {f : ℝ → ℝ → ℝ} {d : TMd} (h : Good f d) {P : TPoly} {r : ℚ} {n : ℕ}
    (hP : d.P = P) (hn : d.n = n) (hr : d.r ≤ r) : Good f ⟨P, r, n⟩ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, le_trans h2 hr⟩
  have := Encl.weaken h1 hr
  rw [hP, hn] at this
  exact this

theorem Good.congr {f g : ℝ → ℝ → ℝ} {d : TMd} (h : Good f d) (hfg : ∀ t ρ, Dom t ρ → f t ρ = g t ρ) :
    Good g d := ⟨Encl.congr h.1 hfg, h.2⟩

/-- bound `|x| ≤ κ t^v` from a TM -/
theorem Good.abs_le' {x : ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) {v : ℕ}
    (hz : zeroPrefix X.P v = true) (hv : v ≤ X.n) {κ : ℚ}
    (hκ : bsum (ldrop (entryBounds X.P) v) + X.r * Tq ^ (X.n - v) ≤ κ) {t ρ : ℝ} (hd : Dom t ρ) :
    |x t ρ| ≤ (κ : ℝ) * t ^ v := by
  have h := hx.abs_le hz hv hd
  have hκ' : ((bsum (ldrop (entryBounds X.P) v) : ℚ) : ℝ) + (X.r : ℝ) * (Tq : ℝ) ^ (X.n - v) ≤ κ := by
    exact_mod_cast hκ
  calc |x t ρ| ≤ t ^ v * ((bsum (ldrop (entryBounds X.P) v) : ℝ) + X.r * (Tq : ℝ) ^ (X.n - v)) := h
    _ ≤ t ^ v * κ := mul_le_mul_of_nonneg_left hκ' (pow_nonneg hd.1.le _)
    _ = κ * t ^ v := by ring

/-! ## coefficient lists -/

def atanhCoeffs (K : ℕ) : List ℚ := (List.range K).map (fun k : ℕ => (1 : ℚ) / (2 * k + 1))
def logCoeffs (m : ℕ) : List ℚ := (List.range m).map (fun i : ℕ => (1 : ℚ) / (i + 1))

theorem hornerR_map_range (f : ℕ → ℚ) (K : ℕ) (z : ℝ) :
    hornerR ((List.range K).map f) z = ∑ k ∈ range K, (f k : ℝ) * z ^ k := by
  rw [hornerR_eq_sum]
  simp only [List.length_map, List.length_range]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  congr 2
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem atanh_horner (K : ℕ) (x : ℝ) :
    x * hornerR (atanhCoeffs K) (x * x) = ∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
  unfold atanhCoeffs
  rw [hornerR_map_range, mul_sum]
  apply sum_congr rfl
  intro k _
  push_cast
  rw [← pow_two, ← pow_mul, pow_succ]
  ring

theorem atanhdiv_horner (K : ℕ) (x : ℝ) :
    hornerR (atanhCoeffs K) (x * x) = ∑ k ∈ range K, x ^ (2 * k) / (2 * (k : ℝ) + 1) := by
  unfold atanhCoeffs
  rw [hornerR_map_range]
  apply sum_congr rfl
  intro k _
  push_cast
  rw [← pow_two, ← pow_mul]
  ring

theorem log_horner (m : ℕ) (z : ℝ) :
    z * hornerR (logCoeffs m) z = ∑ i ∈ range m, z ^ (i + 1) / ((i : ℝ) + 1) := by
  unfold logCoeffs
  rw [hornerR_map_range, mul_sum]
  apply sum_congr rfl
  intro i _
  push_cast
  rw [pow_succ]
  ring

/-! ## series TMs -/

theorem good_atanh {x : ℝ → ℝ → ℝ} {X Y : TMd} (hx : Good x X) (K : ℕ)
    (hz : zeroPrefix X.P 1 = true) (h1 : 1 ≤ X.n)
    (hY : Good (fun t ρ => x t ρ * hornerR (atanhCoeffs K) (x t ρ * x t ρ)) Y)
    (κ : ℚ) (hκ : bsum (ldrop (entryBounds X.P) 1) + X.r * Tq ^ (X.n - 1) ≤ κ) (hκT : κ * Tq < 1)
    (hK : Y.n ≤ 2 * K + 1) (r' : ℚ)
    (hr' : Y.r + κ ^ (2 * K + 1) * Tq ^ (2 * K + 1 - Y.n) / (1 - κ * Tq) ≤ r') :
    Good (fun t ρ => atanhR (x t ρ)) ⟨Y.P, r', Y.n⟩ := by
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
    have hser := atanh_series hx1 K
    have hYe := hY.1 t ρ hd
    simp only at hYe
    rw [atanh_horner] at hYe
    have hden : 0 < 1 - (κ : ℝ) * Tq := by linarith
    have hden' : 1 - (κ : ℝ) * Tq ≤ 1 - |x t ρ| := by linarith
    have hpow : |x t ρ| ^ (2 * K + 1) ≤ ((κ : ℝ) ^ (2 * K + 1) * (Tq : ℝ) ^ (2 * K + 1 - Y.n)) * t ^ Y.n := by
      calc |x t ρ| ^ (2 * K + 1) ≤ ((κ : ℝ) * t) ^ (2 * K + 1) := pow_le_pow_left₀ (abs_nonneg _) hxb _
        _ = (κ : ℝ) ^ (2 * K + 1) * t ^ (2 * K + 1) := by rw [mul_pow]
        _ ≤ (κ : ℝ) ^ (2 * K + 1) * ((Tq : ℝ) ^ (2 * K + 1 - Y.n) * t ^ Y.n) :=
            mul_le_mul_of_nonneg_left (pow_le_T_pow ht0 hd.2.1 hK) (pow_nonneg hκ0 _)
        _ = _ := by ring
    have hA : |atanhR (x t ρ) - ∑ k ∈ range K, x t ρ ^ (2 * k + 1) / (2 * (k : ℝ) + 1)| ≤
        ((κ : ℝ) ^ (2 * K + 1) * (Tq : ℝ) ^ (2 * K + 1 - Y.n) / (1 - κ * Tq)) * t ^ Y.n := by
      refine hser.trans ?_
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - |x t ρ|)]
      calc |x t ρ| ^ (2 * K + 1) ≤ ((κ : ℝ) ^ (2 * K + 1) * (Tq : ℝ) ^ (2 * K + 1 - Y.n)) * t ^ Y.n := hpow
        _ = ((κ : ℝ) ^ (2 * K + 1) * (Tq : ℝ) ^ (2 * K + 1 - Y.n) / (1 - κ * Tq)) * t ^ Y.n *
              (1 - κ * Tq) := by field_simp
        _ ≤ ((κ : ℝ) ^ (2 * K + 1) * (Tq : ℝ) ^ (2 * K + 1 - Y.n) / (1 - κ * Tq)) * t ^ Y.n *
              (1 - |x t ρ|) := by
            apply mul_le_mul_of_nonneg_left hden'
            have : (0 : ℝ) ≤ (Tq : ℝ) ^ (2 * K + 1 - Y.n) := pow_nonneg Tq_pos.le _
            positivity
    have hr'' : (Y.r : ℝ) + (κ : ℝ) ^ (2 * K + 1) * (Tq : ℝ) ^ (2 * K + 1 - Y.n) / (1 - κ * Tq) ≤ r' := by
      have := hr'
      exact_mod_cast this
    show |atanhR (x t ρ) - ev Y.P t ρ| ≤ (r' : ℝ) * t ^ Y.n
    calc |atanhR (x t ρ) - ev Y.P t ρ|
        ≤ |atanhR (x t ρ) - ∑ k ∈ range K, x t ρ ^ (2 * k + 1) / (2 * (k : ℝ) + 1)| +
          |∑ k ∈ range K, x t ρ ^ (2 * k + 1) / (2 * (k : ℝ) + 1) - ev Y.P t ρ| := abs_sub_le _ _ _
      _ ≤ ((κ : ℝ) ^ (2 * K + 1) * (Tq : ℝ) ^ (2 * K + 1 - Y.n) / (1 - κ * Tq)) * t ^ Y.n +
          (Y.r : ℝ) * t ^ Y.n := add_le_add hA hYe
      _ = ((Y.r : ℝ) + (κ : ℝ) ^ (2 * K + 1) * (Tq : ℝ) ^ (2 * K + 1 - Y.n) / (1 - κ * Tq)) * t ^ Y.n := by ring
      _ ≤ (r' : ℝ) * t ^ Y.n := mul_le_mul_of_nonneg_right hr'' (pow_nonneg ht0 _)
  · refine le_trans ?_ hr'
    have hκ0 := hκq
    have : 0 < 1 - κ * Tq := by linarith
    have : (0 : ℚ) ≤ Tq ^ (2 * K + 1 - Y.n) := pow_nonneg Tq_nonneg _
    have : 0 ≤ κ ^ (2 * K + 1) * Tq ^ (2 * K + 1 - Y.n) / (1 - κ * Tq) := by positivity
    linarith

end CKLaneA3X


