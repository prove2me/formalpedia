-- Prove2me | Definitions.Def_CK_CKLaneN23_CSeries
-- name    : CK_CKLaneN23_CSeries
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:50:43.259954+00:00
-- url     : https://prove2.me/theorems/1b13efaa-908b-4cf9-89a5-f2a71c88897b
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CSeries` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CSeries` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CSeries` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CSeries (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CSeries.lean)

import Definitions.Def_CK_CKLaneN23_CTMFun
import Definitions.Def_CK_GeneralCK_Statement

-- ===== source module CKLaneN23.CSeries =====
section

/-!
# CKLaneN23.CSeries — analytic series with explicit power remainders, and the TM tail lemma

(atanh / atanh÷x / log(1-y) parts adapted from Lane A3's `CKLaneA3.Series`.)
* `tmTail_good` : a TM of a polynomial surrogate `P ∘ x` plus a series bound `|g - P| ≤ T|z|^m`
  gives a TM of `g ∘ x`.
* series bounds: geometric, atanh, entropy `hent z = H((1-z)/2)`, `log(1-y)`.
-/

namespace CKLaneN23.CT

open Finset GeneralCK

/-! ## the general tail lemma -/

noncomputable def tmTail (Y : TMd) (X : TMd) (vx : ℕ) (T : ℚ) (m : ℕ) : TMd :=
  ⟨Y.P, rup (Y.r + T * magC X vx ^ m * Eps ^ (vx * m - Y.n)), Y.n⟩

theorem tmTail_good {x : ℝ → ℝ → ℝ → ℝ} {X Y : TMd} {P g : ℝ → ℝ} (hx : Good x X) (vx : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n)
    (hY : Good (fun a σ τ => P (x a σ τ)) Y)
    {T zmax : ℚ} {m : ℕ} (hT : 0 ≤ T)
    (hser : ∀ z : ℝ, |z| ≤ zmax → |g z - P z| ≤ T * |z| ^ m)
    (hmax : magC X vx * Eps ^ vx ≤ zmax) (hord : Y.n ≤ vx * m) :
    Good (fun a σ τ => g (x a σ τ)) (tmTail Y X vx T m) := by
  have hM := magC_nonneg hx vx
  refine ⟨?_, ?_⟩
  · intro a σ τ hd
    have ha0 := hd.1.le
    have hxa := hx.abs_le hz hvx hd
    have hsup : |x a σ τ| ≤ (zmax : ℝ) := by
      have h1 : a ^ vx ≤ (Eps : ℝ) ^ vx := pow_le_pow_left₀ ha0 hd.2.1 vx
      have h2 : ((magC X vx : ℚ) : ℝ) * (Eps : ℝ) ^ vx ≤ zmax := by exact_mod_cast hmax
      calc |x a σ τ| ≤ a ^ vx * (magC X vx : ℝ) := by unfold magC; push_cast; linarith [hxa]
        _ ≤ (Eps : ℝ) ^ vx * (magC X vx : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (by exact_mod_cast hM)
        _ ≤ zmax := by linarith
    have hs := hser (x a σ τ) hsup
    have hh := hY.1 a σ τ hd
    have hpow : |x a σ τ| ^ m ≤ (a ^ vx * (magC X vx : ℝ)) ^ m := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      unfold magC; push_cast; linarith [hxa]
    have hE : (a ^ vx) ^ m ≤ (Eps : ℝ) ^ (vx * m - Y.n) * a ^ Y.n := by
      rw [← pow_mul]; exact pow_le_E_pow ha0 hd.2.1 hord
    have hT' : (0 : ℝ) ≤ T := by exact_mod_cast hT
    have hM' : (0 : ℝ) ≤ magC X vx := by exact_mod_cast hM
    have htail : |g (x a σ τ) - P (x a σ τ)| ≤
        (T : ℝ) * (magC X vx : ℝ) ^ m * (Eps : ℝ) ^ (vx * m - Y.n) * a ^ Y.n := by
      calc |g (x a σ τ) - P (x a σ τ)| ≤ T * |x a σ τ| ^ m := hs
        _ ≤ T * (a ^ vx * (magC X vx : ℝ)) ^ m := mul_le_mul_of_nonneg_left hpow hT'
        _ = T * (magC X vx : ℝ) ^ m * (a ^ vx) ^ m := by rw [mul_pow]; ring
        _ ≤ T * (magC X vx : ℝ) ^ m * ((Eps : ℝ) ^ (vx * m - Y.n) * a ^ Y.n) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by ring
    have hup : ((Y.r + T * magC X vx ^ m * Eps ^ (vx * m - Y.n) : ℚ) : ℝ) ≤
        (rup (Y.r + T * magC X vx ^ m * Eps ^ (vx * m - Y.n)) : ℝ) := by
      exact_mod_cast le_rup _
    push_cast at hup
    show |g (x a σ τ) - ev Y.P a σ τ| ≤ _
    calc |g (x a σ τ) - ev Y.P a σ τ|
        ≤ |g (x a σ τ) - P (x a σ τ)| + |P (x a σ τ) - ev Y.P a σ τ| := abs_sub_le _ _ _
      _ ≤ T * (magC X vx : ℝ) ^ m * (Eps : ℝ) ^ (vx * m - Y.n) * a ^ Y.n + (Y.r : ℝ) * a ^ Y.n :=
          add_le_add htail hh
      _ = ((Y.r : ℝ) + T * (magC X vx : ℝ) ^ m * (Eps : ℝ) ^ (vx * m - Y.n)) * a ^ Y.n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hup (pow_nonneg ha0 _)
  · refine le_trans ?_ (le_rup _)
    have := hY.2
    have := Eps_nonneg
    positivity

/-- variant: the series bound is only needed on `[0, zmax]` when `x ≥ 0` on the domain. -/
theorem tmTail_good_nonneg {x : ℝ → ℝ → ℝ → ℝ} {X Y : TMd} {P g : ℝ → ℝ} (hx : Good x X) (vx : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n)
    (hY : Good (fun a σ τ => P (x a σ τ)) Y)
    (hxpos : ∀ a σ τ, Dom a σ τ → 0 ≤ x a σ τ)
    {T zmax : ℚ} {m : ℕ} (hT : 0 ≤ T)
    (hser : ∀ z : ℝ, 0 ≤ z → z ≤ zmax → |g z - P z| ≤ T * |z| ^ m)
    (hmax : magC X vx * Eps ^ vx ≤ zmax) (hord : Y.n ≤ vx * m) :
    Good (fun a σ τ => g (x a σ τ)) (tmTail Y X vx T m) := by
  -- replace g by a function agreeing with it on [0,∞) and with P elsewhere
  set g' : ℝ → ℝ := fun z => if 0 ≤ z then g z else P z
  have hser' : ∀ z : ℝ, |z| ≤ zmax → |g' z - P z| ≤ T * |z| ^ m := by
    intro z hz
    by_cases h0 : 0 ≤ z
    · simp only [g', if_pos h0]
      exact hser z h0 (le_trans (le_abs_self z) hz)
    · simp only [g', if_neg h0, sub_self, abs_zero]
      have : (0 : ℝ) ≤ T := by exact_mod_cast hT
      positivity
  have h := tmTail_good (g := g') hx vx hz hvx hY hT hser' hmax hord
  refine h.congr ?_
  intro a σ τ hd
  simp only [g', if_pos (hxpos a σ τ hd)]

/-! ## coefficient lists and Horner identities -/

theorem hornerL_map_range_eq (f : ℕ → LPoly) (K : ℕ) (z : ℝ) :
    hornerL ((List.range K).map f) z = ∑ k ∈ range K, LPoly.eval (Real.log 2) (f k) * z ^ k := by
  induction K generalizing f with
  | zero => simp [hornerL_nil]
  | succ K ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hornerL_cons, ih, sum_range_succ',
      mul_sum]
    have hs : ∀ k ∈ range K, z * (LPoly.eval (Real.log 2) ((f ∘ Nat.succ) k) * z ^ k) =
        LPoly.eval (Real.log 2) (f (k + 1)) * z ^ (k + 1) := by
      intro k _
      simp only [Function.comp_apply]
      ring
    rw [sum_congr rfl hs]
    ring

theorem LPoly.eval_const (q : ℚ) : LPoly.eval (Real.log 2) [(0, q)] = (q : ℝ) := by
  simp [LPoly.eval_cons, LPoly.eval_nil]

theorem LPoly.eval_invL (q : ℚ) : LPoly.eval (Real.log 2) [(-1, q)] = (q : ℝ) / Real.log 2 := by
  simp [LPoly.eval_cons, LPoly.eval_nil, zpow_neg, div_eq_mul_inv]

/-- geometric: `[1,1,…,1]` (K ones) -/
def csGeom (K : ℕ) : List LPoly := (List.range K).map (fun _ => [(0, 1)])

theorem hornerL_geom (K : ℕ) (y : ℝ) : hornerL (csGeom K) y = ∑ k ∈ range K, y ^ k := by
  unfold csGeom
  rw [hornerL_map_range_eq]
  apply sum_congr rfl; intro k _
  rw [LPoly.eval_const]; push_cast; ring

/-- atanh: coefficients `1/(2k+1)` (series in `z*z`) -/
def csAt (K : ℕ) : List LPoly := (List.range K).map (fun k : ℕ => [(0, (1 : ℚ) / (2 * k + 1))])

theorem hornerL_at (K : ℕ) (z : ℝ) :
    z * hornerL (csAt K) (z * z) = ∑ k ∈ range K, z ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
  unfold csAt
  rw [hornerL_map_range_eq, mul_sum]
  apply sum_congr rfl; intro k _
  rw [LPoly.eval_const]; push_cast
  rw [← pow_two, ← pow_mul, pow_succ]; ring

theorem hornerL_atdiv (K : ℕ) (w : ℝ) :
    hornerL (csAt K) w = ∑ k ∈ range K, w ^ k / (2 * (k : ℝ) + 1) := by
  unfold csAt
  rw [hornerL_map_range_eq]
  apply sum_congr rfl; intro k _
  rw [LPoly.eval_const]; push_cast; ring

/-- log(1-y): coefficients `1/(i+1)` -/
def csLog (n : ℕ) : List LPoly := (List.range n).map (fun i : ℕ => [(0, (1 : ℚ) / (i + 1))])

theorem hornerL_log (n : ℕ) (y : ℝ) :
    y * hornerL (csLog n) y = ∑ i ∈ range n, y ^ (i + 1) / ((i : ℝ) + 1) := by
  unfold csLog
  rw [hornerL_map_range_eq, mul_sum]
  apply sum_congr rfl; intro i _
  rw [LPoly.eval_const]; push_cast
  rw [pow_succ]; ring

/-- entropy: `1 - (1/(2L)) Σ_{j<K} w^(j+1)/((j+1)(2j+1))` as `[1, c₀, c₁, …]` in `w` -/
def csH (K : ℕ) : List LPoly :=
  [(0, 1)] :: (List.range K).map (fun j : ℕ => [(-1, -(1 : ℚ) / (2 * (j + 1) * (2 * j + 1)))])

theorem hornerL_H (K : ℕ) (w : ℝ) :
    hornerL (csH K) w = 1 - (∑ j ∈ range K, w ^ (j + 1) / (((j : ℝ) + 1) * (2 * j + 1))) / (2 * Real.log 2) := by
  unfold csH
  rw [hornerL_cons, hornerL_map_range_eq, LPoly.eval_const, mul_sum]
  have hL : Real.log 2 ≠ 0 := by positivity
  have hs : ∀ j ∈ range K, w * (LPoly.eval (Real.log 2)
      [(-1, -(1 : ℚ) / (2 * ((j : ℚ) + 1) * (2 * (j : ℚ) + 1)))] * w ^ j) =
      -(w ^ (j + 1) / (((j : ℝ) + 1) * (2 * j + 1)) / (2 * Real.log 2)) := by
    intro j _
    rw [LPoly.eval_invL]
    push_cast
    have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [sum_congr rfl hs, sum_neg_distrib, sum_div]
  push_cast
  ring

/-! ## series bounds -/

noncomputable def atanhR (x : ℝ) : ℝ := Real.log ((1 + x) / (1 - x)) / 2

theorem sum_odd_identity (x : ℝ) (K : ℕ) :
    ∑ i ∈ range (2 * K), (x ^ (i + 1) / ((i : ℝ) + 1) - (-x) ^ (i + 1) / ((i : ℝ) + 1)) =
      2 * ∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h2 : 2 * (K + 1) = 2 * K + 1 + 1 := by ring
    rw [h2, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    have hodd : (-x) ^ (2 * K + 1) = -(x ^ (2 * K + 1)) := Odd.neg_pow ⟨K, rfl⟩ x
    have heven : (-x) ^ (2 * K + 1 + 1) = x ^ (2 * K + 1 + 1) := Even.neg_pow ⟨K + 1, by ring⟩ x
    rw [hodd, heven]
    push_cast
    ring

theorem atanh_series {x : ℝ} (hx : |x| < 1) (K : ℕ) :
    |atanhR x - ∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)| ≤ |x| ^ (2 * K + 1) / (1 - |x|) := by
  have h1 := Real.abs_log_sub_add_sum_range_le hx (2 * K)
  have hx' : |-x| < 1 := by rwa [abs_neg]
  have h2 := Real.abs_log_sub_add_sum_range_le hx' (2 * K)
  rw [abs_neg, sub_neg_eq_add] at h2
  have hp : 0 < 1 + x := by have := (abs_lt.mp hx).1; linarith
  have hm : 0 < 1 - x := by have := (abs_lt.mp hx).2; linarith
  have hlog : Real.log ((1 + x) / (1 - x)) = Real.log (1 + x) - Real.log (1 - x) :=
    Real.log_div hp.ne' hm.ne'
  have hid := sum_odd_identity x K
  rw [sum_sub_distrib] at hid
  set S1 := ∑ i ∈ range (2 * K), x ^ (i + 1) / ((i : ℝ) + 1)
  set S2 := ∑ i ∈ range (2 * K), (-x) ^ (i + 1) / ((i : ℝ) + 1)
  set Sk := ∑ k ∈ range K, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1)
  have hkey : atanhR x - Sk = ((S2 + Real.log (1 + x)) - (S1 + Real.log (1 - x))) / 2 := by
    unfold atanhR; rw [hlog]; linarith
  rw [hkey, abs_div, abs_two]
  have := abs_sub (S2 + Real.log (1 + x)) (S1 + Real.log (1 - x))
  have hden : 0 < 1 - |x| := by linarith
  have e : |x| ^ (2 * K + 1) / (1 - |x|) = (|x| ^ (2 * K + 1) / (1 - |x|) + |x| ^ (2 * K + 1) / (1 - |x|)) / 2 := by ring
  rw [e]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

theorem log1m_series {y : ℝ} (hy : |y| < 1) (n : ℕ) :
    |Real.log (1 - y) + ∑ i ∈ range n, y ^ (i + 1) / ((i : ℝ) + 1)| ≤ |y| ^ (n + 1) / (1 - |y|) := by
  have := Real.abs_log_sub_add_sum_range_le hy n
  rwa [add_comm] at this

theorem hasDerivAt_atanhR {z : ℝ} (hz : |z| < 1) : HasDerivAt atanhR (1 / (1 - z ^ 2)) z := by
  have hp : 0 < 1 + z := by have := (abs_lt.mp hz).1; linarith
  have hm : 0 < 1 - z := by have := (abs_lt.mp hz).2; linarith
  have hnum : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have hden : HasDerivAt (fun z : ℝ => 1 - z) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub 1
  have hq := hnum.div hden hm.ne'
  have hl := hq.log (div_pos hp hm).ne'
  have h2 := hl.div_const 2
  have h1m : (1 : ℝ) - z ≠ 0 := hm.ne'
  have h1p : (1 : ℝ) + z ≠ 0 := hp.ne'
  have h1z : (1 : ℝ) - z ^ 2 ≠ 0 := by
    have : (1 : ℝ) - z ^ 2 = (1 - z) * (1 + z) := by ring
    rw [this]; exact mul_ne_zero h1m h1p
  have key : (1 : ℝ) / (1 - z ^ 2) =
      ((1 * (1 - z) - (1 + z) * (-1)) / (1 - z) ^ 2) / ((1 + z) / (1 - z)) / 2 := by
    field_simp; ring
  rw [key]
  exact h2

/-- geometric series bound -/
theorem geom_series {y : ℝ} (hy : |y| < 1) (K : ℕ) :
    |1 / (1 - y) - ∑ k ∈ range K, y ^ k| ≤ |y| ^ K / (1 - |y|) := by
  have hy1 : y ≠ 1 := by intro h; rw [h] at hy; simp at hy
  have h1 : (1 : ℝ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy1)
  have hs : ∑ k ∈ range K, y ^ k = (1 - y ^ K) / (1 - y) := by
    rw [eq_div_iff h1]
    have := geom_sum_mul y K
    linarith
  rw [hs]
  have e : 1 / (1 - y) - (1 - y ^ K) / (1 - y) = y ^ K / (1 - y) := by field_simp; ring
  rw [e, abs_div, abs_pow]
  have hd : 0 < 1 - |y| := by linarith
  have hd2 : 1 - |y| ≤ |1 - y| := by
    have := abs_sub_abs_le_abs_sub 1 y
    rw [abs_one] at this; linarith
  exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _) hd hd2

/-- entropy in `d`-coordinates -/
noncomputable def hent (z : ℝ) : ℝ := H ((1 - z) / 2)

noncomputable def gfun (z : ℝ) : ℝ := (1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)

theorem hent_eq {z : ℝ} (hz : |z| < 1) : hent z = 1 - gfun z / (2 * Real.log 2) := by
  have hp : 0 < 1 + z := by have := (abs_lt.mp hz).1; linarith
  have hm : 0 < 1 - z := by have := (abs_lt.mp hz).2; linarith
  have hL : Real.log 2 ≠ 0 := by positivity
  unfold hent H Real.binEntropy gfun
  have e1 : Real.log ((1 - z) / 2) = Real.log (1 - z) - Real.log 2 := Real.log_div hm.ne' (by norm_num)
  have e2 : 1 - (1 - z) / 2 = (1 + z) / 2 := by ring
  have e3 : Real.log ((1 + z) / 2) = Real.log (1 + z) - Real.log 2 := Real.log_div hp.ne' (by norm_num)
  rw [e2, Real.log_inv, Real.log_inv, e1, e3]
  field_simp
  ring

theorem hasDerivAt_gfun {z : ℝ} (hz : |z| < 1) : HasDerivAt gfun (2 * atanhR z) z := by
  have hp : 0 < 1 + z := by have := (abs_lt.mp hz).1; linarith
  have hm : 0 < 1 - z := by have := (abs_lt.mp hz).2; linarith
  have h1 : HasDerivAt (fun z : ℝ => 1 + z) 1 z := by simpa using (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun z : ℝ => 1 - z) (-1) z := by simpa using (hasDerivAt_id z).const_sub 1
  have ha := h1.mul (h1.log hp.ne')
  have hb := h2.mul (h2.log hm.ne')
  have h := ha.add hb
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  · unfold atanhR
    rw [Real.log_div hp.ne' hm.ne']
    field_simp
    ring
  · simp [gfun]

noncomputable def atanhRem (K : ℕ) (z : ℝ) : ℝ :=
  atanhR z - ∑ k ∈ range K, z ^ (2 * k + 1) / (2 * (k : ℝ) + 1)

/-- `gfun z = Σ_{j≥0} z^(2j+2)/((j+1)(2j+1))`, remainder `2|z|^(2K+2)/(1-|z|)`. -/
theorem gfun_series {z : ℝ} (hz : |z| < 1) (K : ℕ) :
    |gfun z - ∑ j ∈ range K, z ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * j + 1))| ≤
      2 * |z| ^ (2 * K + 2) / (1 - |z|) := by
  set D : ℝ → ℝ := fun w => gfun w - ∑ j ∈ range K, w ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * j + 1))
  have hD0 : D 0 = 0 := by simp [D, gfun]
  have hderiv : ∀ w : ℝ, |w| < 1 → HasDerivAt D (2 * atanhRem K w) w := by
    intro w hw
    have hg := hasDerivAt_gfun hw
    have hS : HasDerivAt (fun w => ∑ j ∈ range K, w ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * j + 1)))
        (∑ j ∈ range K, 2 * (w ^ (2 * j + 1) / (2 * (j : ℝ) + 1))) w := by
      have := HasDerivAt.fun_sum (u := range K)
        (A := fun j w => w ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * j + 1)))
        (A' := fun j => 2 * (w ^ (2 * j + 1) / (2 * (j : ℝ) + 1))) (x := w) (fun j _ => by
          have h := (hasDerivAt_pow (2 * j + 2) w).div_const (((j : ℝ) + 1) * (2 * j + 1))
          have hk1 : ((j : ℝ) + 1) ≠ 0 := by positivity
          have hk2 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
          refine h.congr_deriv ?_
          rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega]
          push_cast
          field_simp)
      simpa using this
    have h := hg.sub hS
    refine h.congr_deriv ?_
    unfold atanhRem
    rw [mul_sub, mul_sum]
  have hbound : ∀ w : ℝ, |w| ≤ |z| → |2 * atanhRem K w| ≤ 2 * (|z| ^ (2 * K + 1) / (1 - |z|)) := by
    intro w hw
    have hw1 : |w| < 1 := lt_of_le_of_lt hw hz
    rw [abs_mul, abs_two]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have h1 := atanh_series hw1 K
    unfold atanhRem
    refine h1.trans ?_
    have hd1 : 0 < 1 - |z| := by linarith
    have hd2 : 1 - |z| ≤ 1 - |w| := by linarith
    calc |w| ^ (2 * K + 1) / (1 - |w|) ≤ |z| ^ (2 * K + 1) / (1 - |w|) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hw _) (by linarith)
      _ ≤ |z| ^ (2 * K + 1) / (1 - |z|) :=
          div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _) hd1 hd2
  -- mean value on the segment [0, z]
  have hmvt : |D z - D 0| ≤ 2 * (|z| ^ (2 * K + 1) / (1 - |z|)) * |z - 0| := by
    have hconv : Convex ℝ (Set.Icc (-|z|) (|z|)) := convex_Icc _ _
    have hdiff : ∀ w ∈ Set.Icc (-|z|) (|z|), HasDerivWithinAt D (2 * atanhRem K w) (Set.Icc (-|z|) (|z|)) w :=
      fun w hw => (hderiv w (lt_of_le_of_lt (abs_le.mpr ⟨hw.1, hw.2⟩) hz)).hasDerivWithinAt
    have hb : ∀ w ∈ Set.Icc (-|z|) (|z|), ‖2 * atanhRem K w‖ ≤ 2 * (|z| ^ (2 * K + 1) / (1 - |z|)) :=
      fun w hw => by rw [Real.norm_eq_abs]; exact hbound w (abs_le.mpr ⟨hw.1, hw.2⟩)
    have h0 : (0 : ℝ) ∈ Set.Icc (-|z|) (|z|) := ⟨by linarith [abs_nonneg z], abs_nonneg z⟩
    have hz' : z ∈ Set.Icc (-|z|) (|z|) := ⟨neg_abs_le z, le_abs_self z⟩
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hdiff hb h0 hz'
    simpa [Real.norm_eq_abs] using this
  rw [hD0, sub_zero, sub_zero] at hmvt
  have e : 2 * (|z| ^ (2 * K + 1) / (1 - |z|)) * |z| = 2 * |z| ^ (2 * K + 2) / (1 - |z|) := by
    rw [pow_succ]; ring
  rw [e] at hmvt
  exact hmvt

/-- entropy series in `z*z` with remainder `|z|^(2K+2)/(log 2 (1-|z|))`. -/
theorem hent_series {z : ℝ} (hz : |z| < 1) (K : ℕ) :
    |hent z - hornerL (csH K) (z * z)| ≤ |z| ^ (2 * K + 2) / (Real.log 2 * (1 - |z|)) := by
  rw [hent_eq hz, hornerL_H]
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := gfun_series hz K
  have e : ∑ j ∈ range K, (z * z) ^ (j + 1) / (((j : ℝ) + 1) * (2 * j + 1)) =
      ∑ j ∈ range K, z ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * j + 1)) := by
    apply sum_congr rfl; intro j _
    rw [← pow_two, ← pow_mul]; ring_nf
  rw [e]
  have e2 : 1 - gfun z / (2 * Real.log 2) - (1 - (∑ j ∈ range K, z ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * j + 1))) / (2 * Real.log 2)) =
      -(gfun z - ∑ j ∈ range K, z ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * j + 1))) / (2 * Real.log 2) := by ring
  rw [e2, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.log 2)]
  have hd : 0 < 1 - |z| := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ Real.log 2 * (1 - |z|))
  calc |gfun z - ∑ j ∈ range K, z ^ (2 * j + 2) / (((j : ℝ) + 1) * (2 * j + 1))| * (Real.log 2 * (1 - |z|))
      ≤ 2 * |z| ^ (2 * K + 2) / (1 - |z|) * (Real.log 2 * (1 - |z|)) := this
    _ = |z| ^ (2 * K + 2) * (2 * Real.log 2) := by field_simp

end CKLaneN23.CT

end


