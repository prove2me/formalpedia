-- Prove2me | Definitions.Def_CK_CKLaneA3V_Region
-- name    : CK_CKLaneA3V_Region
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T17:49:34.051985+00:00
-- url     : https://prove2.me/theorems/7266ba8c-ef39-4243-9db9-bec3c09d3f1a
-- title:
--   Courtade–Kumar proof module `CKLaneA3V.Region` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3V.Region` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3V.Region` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3V.Region (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3V/Region.lean)

import Definitions.Def_CK_CKLaneA3V_FinalLemmas

/-!
# CKLaneA3V.Region — positivity of a TM-enclosed function on a sub-rectangle

For the direct-chart slots only a sub-rectangle `t ∈ [t0, Tq]`, `σ = ρ - 1/2 ∈ [s0, 1/2]` of the TM
domain is needed.  `grid lo hi f m` checks `f` on the `m` uniform sub-intervals of `[lo, hi]`
(kernel-evaluable `Nat.rec`), and `pos_of_TM_region` turns a nested `t`/`σ` grid check of
`D.r * tb ^ (D.n - k) < lower (Horner box of the valuation-k quotient)` into positivity.
-/

namespace CKLaneA3V

/-- uniform grid check of `f` on the `m` sub-intervals of `[lo, hi]` -/
noncomputable def grid (lo hi : ℚ) (f : ℚ → ℚ → Bool) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => ih && f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m)) m

theorem grid_aux (lo hi : ℚ) (f : ℚ → ℚ → Bool) (m k : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true
      (fun j ih => ih && f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m)) k = true) :
    ∀ j < k, f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m) = true := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    have h' : Nat.rec (motive := fun _ => Bool) true
        (fun j ih => ih && f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m)) k = true ∧
        f (lo + (hi - lo) * (k : ℚ) / m) (lo + (hi - lo) * ((k : ℚ) + 1) / m) = true := by
      simpa using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact ih h'.1 j hj'
    · rw [hj']; exact h'.2

theorem grid_cover (lo hi : ℚ) (hlt : lo < hi) (f : ℚ → ℚ → Bool) (m : ℕ) (hm : 0 < m)
    (h : grid lo hi f m = true) {x : ℝ} (hx1 : (lo : ℝ) ≤ x) (hx2 : x ≤ (hi : ℝ)) :
    ∃ a b : ℚ, f a b = true ∧ (a : ℝ) ≤ x ∧ x ≤ (b : ℝ) := by
  have hall := grid_aux lo hi f m m h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlt' : (lo : ℝ) < hi := by exact_mod_cast hlt
  have hd : (0 : ℝ) < (hi : ℝ) - lo := by linarith
  set y : ℝ := (x - lo) / ((hi : ℝ) - lo) * m with hy
  have hq0 : 0 ≤ (x - lo) / ((hi : ℝ) - lo) := div_nonneg (by linarith) hd.le
  have hq1 : (x - lo) / ((hi : ℝ) - lo) ≤ 1 := by rw [div_le_one hd]; linarith
  have hy0 : 0 ≤ y := by rw [hy]; exact mul_nonneg hq0 hm'.le
  have hy1 : y ≤ m := by
    rw [hy]
    have := mul_le_mul_of_nonneg_right hq1 hm'.le
    linarith
  have e : (x - lo) / ((hi : ℝ) - lo) * ((hi : ℝ) - lo) = x - lo := div_mul_cancel₀ _ hd.ne'
  have hyx : ((hi : ℝ) - lo) * y = (x - lo) * m := by
    rw [hy]; linear_combination (m : ℝ) * e
  let j : ℕ := min (⌊y⌋₊) (m - 1)
  have hj : j < m := by omega
  refine ⟨lo + (hi - lo) * (j : ℚ) / m, lo + (hi - lo) * ((j : ℚ) + 1) / m, hall j hj, ?_, ?_⟩
  · push_cast
    have h1 : (j : ℝ) ≤ y := by
      have : (j : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      exact this.trans (Nat.floor_le hy0)
    have key : ((hi : ℝ) - lo) * j / m ≤ x - lo := by
      rw [div_le_iff₀ hm']
      have := mul_le_mul_of_nonneg_left h1 hd.le
      linarith
    linarith
  · push_cast
    have h2 : y ≤ (j : ℝ) + 1 := by
      by_cases hc : ⌊y⌋₊ ≤ m - 1
      · have : j = ⌊y⌋₊ := min_eq_left hc
        rw [this]; exact (Nat.lt_floor_add_one y).le
      · push Not at hc
        have hj' : j = m - 1 := min_eq_right hc.le
        rw [hj']
        have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; exact hy1
    have key : x - lo ≤ ((hi : ℝ) - lo) * ((j : ℝ) + 1) / m := by
      rw [le_div_iff₀ hm']
      have := mul_le_mul_of_nonneg_left h2 hd.le
      linarith
    linarith

/-- positivity of a TM-enclosed function of valuation `k` on the rectangle
`t ∈ [t0, Tq]`, `ρ - 1/2 ∈ [s0, 1/2]`, from a nested grid check. -/
theorem pos_of_TM_region {f : ℝ → ℝ → ℝ} {D : TMd} (hf : Good f D) (k : ℕ) (hn : k ≤ D.n)
    (hz : zeroPrefix D.P k = true) (t0 s0 : ℚ) (ht0T : t0 < Tq) (hs0 : s0 < 1 / 2)
    (mT mS : ℕ) (hmT : 0 < mT) (hmS : 0 < mS)
    (hB : grid t0 Tq (fun ta tb => grid s0 (1 / 2) (fun a b =>
        decide (D.r * tb ^ (D.n - k) < (tBox ta tb a b (TPoly.drop D.P k)).1)) mS) mT = true) :
    ∀ t ρ, Dom t ρ → (t0 : ℝ) ≤ t → (s0 : ℝ) ≤ ρ - 1 / 2 → 0 < f t ρ := by
  intro t ρ hd ht0' hs0'
  have ht := hd.1
  have hσ := hd.sigma
  have h1 := hf.1 t ρ hd
  unfold ev at h1
  set σ := ρ - 1 / 2 with hσdef
  have hev := zeroPrefix_eval t σ (Real.log 2) D.P k hz
  obtain ⟨ta, tb, htab, hta, htb⟩ := grid_cover t0 Tq ht0T _ mT hmT hB ht0' hd.2.1
  have htab' : grid s0 (1 / 2) (fun a b =>
      decide (D.r * tb ^ (D.n - k) < (tBox ta tb a b (TPoly.drop D.P k)).1)) mS = true := htab
  have hσ2 : σ ≤ ((1 / 2 : ℚ) : ℝ) := by
    have := (abs_le.mp hσ).2
    push_cast; linarith
  obtain ⟨a, b, hab, ha, hb⟩ := grid_cover s0 (1 / 2) hs0 _ mS hmS htab' hs0' hσ2
  have hBlo : (D.r : ℝ) * t ^ (D.n - k) < TPoly.eval t σ (Real.log 2) (TPoly.drop D.P k) := by
    have h := (tBox_spec hta htb ha hb (TPoly.drop D.P k)).1
    have hq : D.r * tb ^ (D.n - k) < (tBox ta tb a b (TPoly.drop D.P k)).1 := by simpa using hab
    have hq' : (D.r : ℝ) * (tb : ℝ) ^ (D.n - k) < ((tBox ta tb a b (TPoly.drop D.P k)).1 : ℝ) := by
      exact_mod_cast hq
    have hr : (0 : ℝ) ≤ D.r := by exact_mod_cast hf.2
    have hpow : t ^ (D.n - k) ≤ (tb : ℝ) ^ (D.n - k) := pow_le_pow_left₀ ht.le htb _
    have : (D.r : ℝ) * t ^ (D.n - k) ≤ D.r * (tb : ℝ) ^ (D.n - k) := mul_le_mul_of_nonneg_left hpow hr
    linarith
  have hsplit : (D.r : ℝ) * t ^ D.n = t ^ k * ((D.r : ℝ) * t ^ (D.n - k)) := by
    have : D.n = (D.n - k) + k := by omega
    conv_lhs => rw [this]
    ring
  have h2 := neg_abs_le (f t ρ - TPoly.eval t σ (Real.log 2) D.P)
  rw [hsplit] at h1
  have hpos : 0 < t ^ k * (TPoly.eval t σ (Real.log 2) (TPoly.drop D.P k) - D.r * t ^ (D.n - k)) := by
    have : 0 < TPoly.eval t σ (Real.log 2) (TPoly.drop D.P k) - D.r * t ^ (D.n - k) := by linarith
    positivity
  have key : TPoly.eval t σ (Real.log 2) D.P - t ^ k * ((D.r : ℝ) * t ^ (D.n - k)) =
      t ^ k * (TPoly.eval t σ (Real.log 2) (TPoly.drop D.P k) - D.r * t ^ (D.n - k)) := by
    rw [hev]; ring
  linarith

end CKLaneA3V


