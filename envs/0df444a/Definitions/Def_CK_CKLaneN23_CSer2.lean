-- Prove2me | Definitions.Def_CK_CKLaneN23_CSer2
-- name    : CK_CKLaneN23_CSer2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:55:43.904243+00:00
-- url     : https://prove2.me/theorems/cc1c87e6-1059-4bb9-a495-8aa88e4d1fff
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CSer2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CSer2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CSer2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CSer2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CSer2.lean)

import Definitions.Def_CK_CKLaneN23_CSeries

-- ===== source module CKLaneN23.CSer2 =====
section

/-!
# CKLaneN23.CSer2 — chain-ready series bounds (Lane N23b)

All bounds are stated for rational `zmax = 1/16` and rational tail constants, in the exact shape
consumed by `tmTail_good` / `tmTail_good_nonneg`:
* `ser_geom`   : `1/(1-y)`                 vs `hornerL (csGeom K) y`,  tail `16/15 |y|^K`
* `ser_hentSq` : `hent (√Y)` (`Y ≥ 0`)      vs `hornerL (csH K) Y`,     tail `2 |Y|^(K+1)`
* `ser_Adiv`   : `Adiv Y = atanh(√Y)/√Y`    vs `hornerL (csAt K) Y`,    tail `4/3 |Y|^K`
* `ser_log1m`  : `log (1-y)`               vs `-(y · hornerL (csLog n) y)`, tail `16/15 |y|^(n+1)`
* `ser_B`      : `Bfun R = ((1+R) Adiv R - 1)/R` vs `hornerL (csB K) R`, tail `2 |R|^K`
-/

namespace CKLaneN23.CT

open Finset GeneralCK

/-- `A(Y) = atanh(√Y)/√Y`, with `A(Y) = 1` for `Y ≤ 0`. -/
noncomputable def Adiv (Y : ℝ) : ℝ := if Y ≤ 0 then 1 else atanhR (Real.sqrt Y) / Real.sqrt Y

theorem Adiv_of_pos {x : ℝ} (hx : 0 < x) : Adiv (x ^ 2) = atanhR x / x := by
  unfold Adiv
  rw [if_neg (not_le.mpr (by positivity)), Real.sqrt_sq hx.le]

theorem Adiv_zero : Adiv 0 = 1 := by simp [Adiv]

theorem q16 : ((1 / 16 : ℚ) : ℝ) = 1 / 16 := by norm_num

theorem sqrt_le_quarter {Y : ℝ} (h1 : Y ≤ 1 / 16) : Real.sqrt Y ≤ 1 / 4 := by
  have : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← this]
  exact Real.sqrt_le_sqrt h1

theorem log2_gt : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

/-- geometric series, `|y| ≤ 1/16` -/
theorem ser_geom (K : ℕ) : ∀ y : ℝ, |y| ≤ ((1 / 16 : ℚ) : ℝ) →
    |1 / (1 - y) - hornerL (csGeom K) y| ≤ ((16 / 15 : ℚ) : ℝ) * |y| ^ K := by
  intro y hy
  rw [q16] at hy
  have hy1 : |y| < 1 := by linarith
  rw [hornerL_geom]
  have h := geom_series hy1 K
  have hd : 0 < 1 - |y| := by linarith
  refine h.trans ?_
  rw [div_le_iff₀ hd]
  have hp : (0 : ℝ) ≤ |y| ^ K := pow_nonneg (abs_nonneg _) _
  have hk : (1 : ℝ) ≤ (16 / 15) * (1 - |y|) := by linarith
  have e : ((16 / 15 : ℚ) : ℝ) * |y| ^ K * (1 - |y|) = |y| ^ K * ((16 / 15) * (1 - |y|)) := by
    push_cast; ring
  rw [e]
  calc |y| ^ K = |y| ^ K * 1 := by ring
    _ ≤ |y| ^ K * ((16 / 15) * (1 - |y|)) := mul_le_mul_of_nonneg_left hk hp

/-- entropy in the squared variable, `0 ≤ Y ≤ 1/16` -/
theorem ser_hentSq (K : ℕ) : ∀ Y : ℝ, 0 ≤ Y → Y ≤ ((1 / 16 : ℚ) : ℝ) →
    |hent (Real.sqrt Y) - hornerL (csH K) Y| ≤ ((2 : ℚ) : ℝ) * |Y| ^ (K + 1) := by
  intro Y h0 h1
  rw [q16] at h1
  set z := Real.sqrt Y with hz
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz4 : z ≤ 1 / 4 := sqrt_le_quarter h1
  have hzz : z * z = Y := Real.mul_self_sqrt h0
  have habs : |z| = z := abs_of_nonneg hz0
  have hz1 : |z| < 1 := by rw [habs]; linarith
  have h := hent_series hz1 K
  rw [hzz, habs] at h
  refine h.trans ?_
  have hL := log2_gt
  have hpow : z ^ (2 * K + 2) = |Y| ^ (K + 1) := by
    rw [abs_of_nonneg h0, ← hzz, show 2 * K + 2 = 2 * (K + 1) by ring, pow_mul]; ring
  rw [hpow]
  have hd : 0 < Real.log 2 * (1 - z) := mul_pos (by linarith) (by linarith)
  rw [div_le_iff₀ hd]
  have hp : (0 : ℝ) ≤ |Y| ^ (K + 1) := pow_nonneg (abs_nonneg _) _
  have hk : (1 : ℝ) ≤ 2 * (Real.log 2 * (1 - z)) := by nlinarith
  have e : ((2 : ℚ) : ℝ) * |Y| ^ (K + 1) * (Real.log 2 * (1 - z)) =
      |Y| ^ (K + 1) * (2 * (Real.log 2 * (1 - z))) := by push_cast; ring
  rw [e]
  calc |Y| ^ (K + 1) = |Y| ^ (K + 1) * 1 := by ring
    _ ≤ |Y| ^ (K + 1) * (2 * (Real.log 2 * (1 - z))) := mul_le_mul_of_nonneg_left hk hp

/-- `atanh(√Y)/√Y`, `0 ≤ Y ≤ 1/16` -/
theorem ser_Adiv (K : ℕ) : ∀ Y : ℝ, 0 ≤ Y → Y ≤ ((1 / 16 : ℚ) : ℝ) →
    |Adiv Y - hornerL (csAt K) Y| ≤ ((4 / 3 : ℚ) : ℝ) * |Y| ^ K := by
  intro Y h0 h1
  rw [q16] at h1
  rcases h0.lt_or_eq with hpos | hzero
  · set x := Real.sqrt Y with hxdef
    have hx : 0 < x := Real.sqrt_pos.mpr hpos
    have hx4 : x ≤ 1 / 4 := sqrt_le_quarter h1
    have hxx : x ^ 2 = Y := Real.sq_sqrt h0
    have hA : Adiv Y = atanhR x / x := by rw [← hxx]; exact Adiv_of_pos hx
    rw [hA, hornerL_atdiv, ← hxx]
    have hs := atanh_series (x := x) (by rw [abs_of_pos hx]; linarith) K
    have e : atanhR x / x - ∑ k ∈ range K, (x ^ 2) ^ k / (2 * (k : ℝ) + 1) =
        (atanhR x - ∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) / x := by
      rw [sub_div, sum_div]
      congr 1
      apply sum_congr rfl
      intro k _
      rw [← pow_mul, pow_succ]
      field_simp
    rw [e, abs_div, abs_of_pos hx, div_le_iff₀ hx]
    refine hs.trans ?_
    rw [abs_of_pos hx, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
    have hd : 0 < 1 - x := by linarith
    rw [div_le_iff₀ hd]
    have hp : (0 : ℝ) ≤ x ^ (2 * K + 1) := by positivity
    have hk : (1 : ℝ) ≤ (4 / 3) * (1 - x) := by linarith
    have e2 : ((4 / 3 : ℚ) : ℝ) * (x ^ 2) ^ K * x * (1 - x) = x ^ (2 * K + 1) * ((4 / 3) * (1 - x)) := by
      rw [← pow_mul, pow_succ]; push_cast; ring
    rw [e2]
    calc x ^ (2 * K + 1) = x ^ (2 * K + 1) * 1 := by ring
      _ ≤ x ^ (2 * K + 1) * ((4 / 3) * (1 - x)) := mul_le_mul_of_nonneg_left hk hp
  · subst hzero
    rw [Adiv_zero, hornerL_atdiv]
    cases K with
    | zero => norm_num
    | succ K =>
      rw [sum_range_succ']
      simp

/-- `log (1-y)`, `|y| ≤ 1/16`, in the TM form `-(y * hornerL (csLog n) y)` -/
theorem ser_log1m (n : ℕ) : ∀ y : ℝ, |y| ≤ ((1 / 16 : ℚ) : ℝ) →
    |Real.log (1 - y) - ((-1 : ℚ) : ℝ) * (y * hornerL (csLog n) y)| ≤
      ((16 / 15 : ℚ) : ℝ) * |y| ^ (n + 1) := by
  intro y hy
  rw [q16] at hy
  have hy1 : |y| < 1 := by linarith
  have h := log1m_series hy1 n
  rw [hornerL_log]
  have e : Real.log (1 - y) - ((-1 : ℚ) : ℝ) * ∑ i ∈ range n, y ^ (i + 1) / ((i : ℝ) + 1) =
      Real.log (1 - y) + ∑ i ∈ range n, y ^ (i + 1) / ((i : ℝ) + 1) := by push_cast; ring
  rw [e]
  refine h.trans ?_
  have hd : 0 < 1 - |y| := by linarith
  rw [div_le_iff₀ hd]
  have hp : (0 : ℝ) ≤ |y| ^ (n + 1) := pow_nonneg (abs_nonneg _) _
  have hk : (1 : ℝ) ≤ (16 / 15) * (1 - |y|) := by linarith
  have e2 : ((16 / 15 : ℚ) : ℝ) * |y| ^ (n + 1) * (1 - |y|) = |y| ^ (n + 1) * ((16 / 15) * (1 - |y|)) := by
    push_cast; ring
  rw [e2]
  calc |y| ^ (n + 1) = |y| ^ (n + 1) * 1 := by ring
    _ ≤ |y| ^ (n + 1) * ((16 / 15) * (1 - |y|)) := mul_le_mul_of_nonneg_left hk hp

/-! ## the curvature series `B` -/

/-- `B(R) = ((1+R) A(R) - 1)/R`, `B(R) = 4/3` for `R ≤ 0`. -/
noncomputable def Bfun (R : ℝ) : ℝ := if R ≤ 0 then 4 / 3 else ((1 + R) * Adiv R - 1) / R

/-- `B` coefficients `4(j+1)/(4(j+1)^2-1)` -/
def csB (K : ℕ) : List LPoly :=
  (List.range K).map (fun j : ℕ => [(0, (4 * ((j : ℚ) + 1)) / (4 * ((j : ℚ) + 1) ^ 2 - 1))])

theorem hornerL_B (K : ℕ) (R : ℝ) :
    hornerL (csB K) R = ∑ j ∈ range K, 4 * ((j : ℝ) + 1) / (4 * ((j : ℝ) + 1) ^ 2 - 1) * R ^ j := by
  unfold csB
  rw [hornerL_map_range_eq]
  apply sum_congr rfl
  intro j _
  rw [LPoly.eval_const]
  push_cast
  ring

theorem AB_identity (K : ℕ) (R : ℝ) :
    (1 + R) * (∑ k ∈ range (K + 1), R ^ k / (2 * (k : ℝ) + 1)) - 1 =
      R * (∑ j ∈ range K, 4 * ((j : ℝ) + 1) / (4 * ((j : ℝ) + 1) ^ 2 - 1) * R ^ j) +
        R ^ (K + 1) / (2 * (K : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hL : ∑ k ∈ range (K + 1 + 1), R ^ k / (2 * (k : ℝ) + 1) =
        ∑ k ∈ range (K + 1), R ^ k / (2 * (k : ℝ) + 1) + R ^ (K + 1) / (2 * ((K + 1 : ℕ) : ℝ) + 1) :=
      Finset.sum_range_succ _ _
    have hR : ∑ j ∈ range (K + 1), 4 * ((j : ℝ) + 1) / (4 * ((j : ℝ) + 1) ^ 2 - 1) * R ^ j =
        ∑ j ∈ range K, 4 * ((j : ℝ) + 1) / (4 * ((j : ℝ) + 1) ^ 2 - 1) * R ^ j +
          4 * ((K : ℝ) + 1) / (4 * ((K : ℝ) + 1) ^ 2 - 1) * R ^ K :=
      Finset.sum_range_succ _ _
    rw [hL, hR]
    have h1 : (2 * (K : ℝ) + 1) ≠ 0 := by positivity
    have h5 : (2 * (K : ℝ) + 3) ≠ 0 := by positivity
    have hc : 4 * ((K : ℝ) + 1) / (4 * ((K : ℝ) + 1) ^ 2 - 1) =
        1 / (2 * (K : ℝ) + 1) + 1 / (2 * (K : ℝ) + 3) := by
      have e : (4 * ((K : ℝ) + 1) ^ 2 - 1) = (2 * (K : ℝ) + 1) * (2 * (K : ℝ) + 3) := by ring
      rw [e]
      field_simp
      ring
    have e2 : (2 * ((K + 1 : ℕ) : ℝ) + 1) = 2 * (K : ℝ) + 3 := by push_cast; ring
    have key : (1 + R) * (R ^ (K + 1) / (2 * ((K + 1 : ℕ) : ℝ) + 1)) =
        R * (4 * ((K : ℝ) + 1) / (4 * ((K : ℝ) + 1) ^ 2 - 1) * R ^ K) +
          R ^ (K + 1 + 1) / (2 * ((K + 1 : ℕ) : ℝ) + 1) - R ^ (K + 1) / (2 * (K : ℝ) + 1) := by
      rw [hc, e2, pow_succ, pow_succ]
      field_simp
      ring
    linear_combination ih + key

theorem ser_B (K : ℕ) (hK : 1 ≤ K) : ∀ R : ℝ, 0 ≤ R → R ≤ ((1 / 16 : ℚ) : ℝ) →
    |Bfun R - hornerL (csB K) R| ≤ ((2 : ℚ) : ℝ) * |R| ^ K := by
  intro R h0 h1
  have h1' : R ≤ 1 / 16 := by rw [q16] at h1; exact h1
  rw [hornerL_B]
  rcases h0.lt_or_eq with hpos | hzero
  · have hB : Bfun R = ((1 + R) * Adiv R - 1) / R := by unfold Bfun; rw [if_neg (by linarith)]
    have hA := ser_Adiv (K + 1) R h0 h1
    rw [hornerL_atdiv] at hA
    set A' := ∑ k ∈ range (K + 1), R ^ k / (2 * (k : ℝ) + 1) with hA'
    set BK := ∑ j ∈ range K, 4 * ((j : ℝ) + 1) / (4 * ((j : ℝ) + 1) ^ 2 - 1) * R ^ j with hBK
    have hid := AB_identity K R
    rw [← hA', ← hBK] at hid
    have e : Bfun R - BK = ((1 + R) * (Adiv R - A') + R ^ (K + 1) / (2 * (K : ℝ) + 1)) / R := by
      rw [hB, eq_div_iff hpos.ne', sub_mul, div_mul_cancel₀ _ hpos.ne']
      linear_combination hid
    rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hA2 : |Adiv R - A'| ≤ 4 / 3 * R ^ (K + 1) := by
      rw [abs_of_pos hpos] at hA; push_cast at hA; exact hA
    have hK3 : (3 : ℝ) ≤ 2 * (K : ℝ) + 1 := by
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    have hpk : 0 ≤ R ^ (K + 1) := by positivity
    have hq : R ^ (K + 1) / (2 * (K : ℝ) + 1) ≤ R ^ (K + 1) / 3 :=
      div_le_div_of_nonneg_left hpk (by norm_num) hK3
    have hq0 : 0 ≤ R ^ (K + 1) / (2 * (K : ℝ) + 1) := by positivity
    calc |(1 + R) * (Adiv R - A') + R ^ (K + 1) / (2 * (K : ℝ) + 1)|
        ≤ |(1 + R) * (Adiv R - A')| + |R ^ (K + 1) / (2 * (K : ℝ) + 1)| := abs_add_le _ _
      _ = (1 + R) * |Adiv R - A'| + R ^ (K + 1) / (2 * (K : ℝ) + 1) := by
          rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + R), abs_of_nonneg hq0]
      _ ≤ (1 + 1 / 16) * (4 / 3 * R ^ (K + 1)) + R ^ (K + 1) / 3 := by
          apply add_le_add _ hq
          apply mul_le_mul (by linarith) hA2 (abs_nonneg _) (by norm_num)
      _ ≤ ((2 : ℚ) : ℝ) * R ^ K * R := by
          rw [pow_succ]; push_cast
          have : 0 ≤ R ^ K * R := by positivity
          nlinarith
  · subst hzero
    have hb0 : Bfun 0 = 4 / 3 := by simp [Bfun]
    rw [hb0]
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    rw [sum_range_succ']
    simp
    norm_num

end CKLaneN23.CT

end


