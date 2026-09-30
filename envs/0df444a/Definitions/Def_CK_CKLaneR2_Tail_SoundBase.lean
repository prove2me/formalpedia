-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundBase
-- name    : CK_CKLaneR2_Tail_SoundBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T03:37:32.501354+00:00
-- url     : https://prove2.me/theorems/eb4f1473-0542-4831-8c3e-0c6f83b38921
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundBase.lean)

import Definitions.Def_CK_CKLaneR2_Cell_SoundContact
import Definitions.Def_CK_CKLaneR2_Tail_Defs

-- ===== source module CKLaneR2.Tail.SoundBase =====
section

/-!
# Lane R2 — tail checker soundness, part 1: exp polynomials, the `g1` series, generic helpers
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

/-- `g1 v = -(1-v) ln(1-v) / v` (with the removable value `g1 0 = 1`). -/
noncomputable def g1 (v : ℝ) : ℝ := if v = 0 then 1 else -(1 - v) * Real.log (1 - v) / v

theorem abs_add5 (a b c d e : ℝ) : |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  linarith

/-- Perturbing the represented function by at most `δ/one` costs `δ` units of remainder. -/
theorem Contains.perturb {T : TM} {f g : ℝ → ℝ → ℝ → ℝ} (h : Contains one T f) (δ : ℕ)
    (hfg : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → |g x y z - f x y z| ≤ (δ : ℝ) / one) :
    Contains one ⟨T.p, T.r + δ, T.ok⟩ g := by
  intro hok x y z hx hy hz
  have h1 := h hok x y z hx hy hz
  have h2 := hfg x y z hx hy hz
  simp only
  calc |g x y z - evalP 0 T.p x y z / one| ≤ |g x y z - f x y z| + |f x y z - evalP 0 T.p x y z / one| := by
        have := abs_add_le (g x y z - f x y z) (f x y z - evalP 0 T.p x y z / one)
        rw [show g x y z - f x y z + (f x y z - evalP 0 T.p x y z / one) = g x y z - evalP 0 T.p x y z / one by ring]
          at this
        exact this
    _ ≤ (δ : ℝ) / one + (T.r : ℝ) / one := add_le_add h2 h1
    _ = ((T.r + δ : ℕ) : ℝ) / one := by push_cast; ring

/-! ## Exp polynomials -/

theorem evalP_expPoly (e0 e1 e2 e3 e4 : Int) (x y z : ℝ) :
    evalP 0 [[[e0]], [[e1]], [[e2]], [[e3]], [[e4]]] x y z
      = e0 + e1 * z + e2 * z ^ 2 + e3 * z ^ 3 + e4 * z ^ 4 := by
  simp [evalP, evalC, evalR]; ring

theorem evalP_expPolyx (e0 e1 e2 e3 e4 : Int) (x y z : ℝ) :
    evalP 0 [[[e0]], [[], [e1]], [[], [], [e2]], [[], [], [], [e3]], [[], [], [], [], [e4]]] x y z
      = e0 + e1 * x + e2 * x ^ 2 + e3 * x ^ 3 + e4 * x ^ 4 := by
  simp [evalP, evalC, evalR]; ring

theorem expCoef_err (sc : Int) (n d k : Nat) (hd : 0 < d) :
    |(expCoef sc n d k : ℝ) - (sc : ℝ) * (-((n : ℝ) / d)) ^ k / (Nat.factorial k)| ≤ 1 := by
  unfold expCoef
  have hpos : (0 : ℤ) < ((d ^ k * Nat.factorial k : ℕ) : ℤ) := by
    have : 0 < d ^ k * Nat.factorial k := Nat.mul_pos (pow_pos hd k) (Nat.factorial_pos k)
    exact_mod_cast this
  have h := ediv_err (sc * (-(n : ℤ)) ^ k) ((d ^ k * Nat.factorial k : ℕ) : ℤ) hpos
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hf : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have e : ((sc * (-(n : ℤ)) ^ k : ℤ) : ℝ) / (((d ^ k * Nat.factorial k : ℕ) : ℤ) : ℝ)
      = (sc : ℝ) * (-((n : ℝ) / d)) ^ k / (Nat.factorial k) := by
    rw [← neg_div, div_pow]
    push_cast
    field_simp
  rw [e] at h
  exact h

/-- The exp-polynomial error bound (both axes): the real function `(sc/one) exp(-(n/d) w)`. -/
theorem expPoly_err (sc : Int) (n d : Nat) (hsc : 0 < sc) (hd : 0 < d) (hnd : n ≤ d) (w : ℝ) (hw : |w| ≤ 1) :
    |(sc : ℝ) / one * Real.exp (-((n : ℝ) / d) * w)
      - ((expCoef sc n d 0 : ℝ) + expCoef sc n d 1 * w + expCoef sc n d 2 * w ^ 2 + expCoef sc n d 3 * w ^ 3
          + expCoef sc n d 4 * w ^ 4) / one| ≤ (expRem sc n d : ℝ) / one := by
  have hone' : (0 : ℝ) < one := CKLaneR2.Cell.hone'
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : 0 ≤ (n : ℝ) / d := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hr1 : (n : ℝ) / d ≤ 1 := by rw [div_le_one hd']; exact_mod_cast hnd
  have hyr : |(-((n : ℝ) / d) * w)| ≤ (n : ℝ) / d := by
    rw [abs_mul, abs_neg, abs_of_nonneg hr0]
    calc (n : ℝ) / d * |w| ≤ (n : ℝ) / d * 1 := mul_le_mul_of_nonneg_left hw hr0
      _ = (n : ℝ) / d := by ring
  have hy1 : |(-((n : ℝ) / d) * w)| ≤ 1 := hyr.trans hr1
  have hexp := Real.exp_bound hy1 (n := 5) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 5, (-((n : ℝ) / d) * w) ^ m / (m.factorial : ℝ)
      = 1 + (-((n : ℝ) / d) * w) + (-((n : ℝ) / d) * w) ^ 2 / 2 + (-((n : ℝ) / d) * w) ^ 3 / 6
        + (-((n : ℝ) / d) * w) ^ 4 / 24 := by
    simp [Finset.sum_range_succ, Nat.factorial]; try ring
  rw [hsum] at hexp
  have hy5 : |(-((n : ℝ) / d) * w)| ^ 5 ≤ ((n : ℝ) / d) ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hyr 5
  have hc : |(-((n : ℝ) / d) * w)| ^ 5 * (((Nat.succ 5 : ℕ) : ℝ) / ((Nat.factorial 5 : ℕ) * ((5 : ℕ) : ℝ)))
      = |(-((n : ℝ) / d) * w)| ^ 5 / 100 := by
    norm_num [Nat.factorial] <;> ring
  rw [hc] at hexp
  -- the exact Taylor polynomial in w
  have hexact : (sc : ℝ) * (1 + (-((n : ℝ) / d) * w) + (-((n : ℝ) / d) * w) ^ 2 / 2 + (-((n : ℝ) / d) * w) ^ 3 / 6
        + (-((n : ℝ) / d) * w) ^ 4 / 24)
      = (sc : ℝ) * (-((n : ℝ) / d)) ^ 0 / (Nat.factorial 0) + (sc : ℝ) * (-((n : ℝ) / d)) ^ 1 / (Nat.factorial 1) * w
        + (sc : ℝ) * (-((n : ℝ) / d)) ^ 2 / (Nat.factorial 2) * w ^ 2
        + (sc : ℝ) * (-((n : ℝ) / d)) ^ 3 / (Nat.factorial 3) * w ^ 3
        + (sc : ℝ) * (-((n : ℝ) / d)) ^ 4 / (Nat.factorial 4) * w ^ 4 := by
    simp only [Nat.factorial]; push_cast; ring
  have hwk : ∀ k : ℕ, |w| ^ k ≤ 1 := fun k => pow_le_one₀ (abs_nonneg w) hw
  have hterm : ∀ k : ℕ, |(expCoef sc n d k : ℝ) * w ^ k - (sc : ℝ) * (-((n : ℝ) / d)) ^ k / (Nat.factorial k) * w ^ k|
      ≤ 1 := by
    intro k
    rw [← sub_mul, abs_mul, abs_pow]
    calc _ ≤ 1 * 1 := mul_le_mul (expCoef_err sc n d k hd) (hwk k) (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have t0 := hterm 0
  have t1 := hterm 1
  have t2 := hterm 2
  have t3 := hterm 3
  have t4 := hterm 4
  simp only [pow_zero, mul_one, pow_one] at t0 t1
  have hpoly := abs_add5
    ((expCoef sc n d 0 : ℝ) - (sc : ℝ) * (-((n : ℝ) / d)) ^ 0 / (Nat.factorial 0))
    ((expCoef sc n d 1 : ℝ) * w - (sc : ℝ) * (-((n : ℝ) / d)) ^ 1 / (Nat.factorial 1) * w)
    ((expCoef sc n d 2 : ℝ) * w ^ 2 - (sc : ℝ) * (-((n : ℝ) / d)) ^ 2 / (Nat.factorial 2) * w ^ 2)
    ((expCoef sc n d 3 : ℝ) * w ^ 3 - (sc : ℝ) * (-((n : ℝ) / d)) ^ 3 / (Nat.factorial 3) * w ^ 3)
    ((expCoef sc n d 4 : ℝ) * w ^ 4 - (sc : ℝ) * (-((n : ℝ) / d)) ^ 4 / (Nat.factorial 4) * w ^ 4)
  simp only [pow_zero, mul_one, pow_one] at hpoly
  have hsc' : (0 : ℝ) < sc := by exact_mod_cast hsc
  have hscN : ((sc.toNat : ℕ) : ℝ) = (sc : ℝ) := by
    have : ((sc.toNat : ℤ)) = sc := Int.toNat_of_nonneg hsc.le
    exact_mod_cast this
  have hcd := le_cdiv (sc.toNat * n ^ 5) (100 * d ^ 5) (by positivity)
  have hcd' : (sc : ℝ) * ((n : ℝ) / d) ^ 5 / 100 ≤ (cdiv (sc.toNat * n ^ 5) (100 * d ^ 5) : ℝ) := by
    refine le_trans (le_of_eq ?_) hcd
    push_cast; rw [hscN, div_pow]; field_simp
  have hmain : |(sc : ℝ) * Real.exp (-((n : ℝ) / d) * w)
      - ((expCoef sc n d 0 : ℝ) + expCoef sc n d 1 * w + expCoef sc n d 2 * w ^ 2 + expCoef sc n d 3 * w ^ 3
          + expCoef sc n d 4 * w ^ 4)| ≤ (sc : ℝ) * ((n : ℝ) / d) ^ 5 / 100 + 5 := by
    have e : (sc : ℝ) * Real.exp (-((n : ℝ) / d) * w)
        - ((expCoef sc n d 0 : ℝ) + expCoef sc n d 1 * w + expCoef sc n d 2 * w ^ 2 + expCoef sc n d 3 * w ^ 3
          + expCoef sc n d 4 * w ^ 4)
        = (sc : ℝ) * (Real.exp (-((n : ℝ) / d) * w) - (1 + (-((n : ℝ) / d) * w) + (-((n : ℝ) / d) * w) ^ 2 / 2
            + (-((n : ℝ) / d) * w) ^ 3 / 6 + (-((n : ℝ) / d) * w) ^ 4 / 24))
          - (((expCoef sc n d 0 : ℝ) - (sc : ℝ) * (-((n : ℝ) / d)) ^ 0 / (Nat.factorial 0))
            + ((expCoef sc n d 1 : ℝ) * w - (sc : ℝ) * (-((n : ℝ) / d)) ^ 1 / (Nat.factorial 1) * w)
            + ((expCoef sc n d 2 : ℝ) * w ^ 2 - (sc : ℝ) * (-((n : ℝ) / d)) ^ 2 / (Nat.factorial 2) * w ^ 2)
            + ((expCoef sc n d 3 : ℝ) * w ^ 3 - (sc : ℝ) * (-((n : ℝ) / d)) ^ 3 / (Nat.factorial 3) * w ^ 3)
            + ((expCoef sc n d 4 : ℝ) * w ^ 4 - (sc : ℝ) * (-((n : ℝ) / d)) ^ 4 / (Nat.factorial 4) * w ^ 4)) := by
      rw [mul_sub, hexact]; ring
    rw [e]
    simp only [pow_zero, mul_one, pow_one] at *
    calc _ ≤ |(sc : ℝ) * (Real.exp (-((n : ℝ) / d) * w) - (1 + (-((n : ℝ) / d) * w) + (-((n : ℝ) / d) * w) ^ 2 / 2
            + (-((n : ℝ) / d) * w) ^ 3 / 6 + (-((n : ℝ) / d) * w) ^ 4 / 24))| + _ := abs_sub _ _
      _ ≤ (sc : ℝ) * (((n : ℝ) / d) ^ 5 / 100) + (1 + 1 + 1 + 1 + 1) := by
          rw [abs_mul, abs_of_pos hsc']
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ hsc'.le
            have : |(-((n : ℝ) / d) * w)| ^ 5 / 100 ≤ ((n : ℝ) / d) ^ 5 / 100 := by linarith
            linarith
          · linarith
      _ = (sc : ℝ) * ((n : ℝ) / d) ^ 5 / 100 + 5 := by ring
  have e2 : (sc : ℝ) / one * Real.exp (-((n : ℝ) / d) * w)
      - ((expCoef sc n d 0 : ℝ) + expCoef sc n d 1 * w + expCoef sc n d 2 * w ^ 2 + expCoef sc n d 3 * w ^ 3
          + expCoef sc n d 4 * w ^ 4) / one
      = ((sc : ℝ) * Real.exp (-((n : ℝ) / d) * w)
      - ((expCoef sc n d 0 : ℝ) + expCoef sc n d 1 * w + expCoef sc n d 2 * w ^ 2 + expCoef sc n d 3 * w ^ 3
          + expCoef sc n d 4 * w ^ 4)) / one := by ring
  rw [e2, abs_div, abs_of_pos hone']
  apply div_le_div_of_nonneg_right _ hone'.le
  unfold expRem; push_cast
  linarith

theorem expPoly_contains (sc : Int) (n d : Nat) (hsc : 0 < sc) (hd : 0 < d) (hnd : n ≤ d) :
    Contains one (expPolyTM sc n d) (fun _ _ z => (sc : ℝ) / one * Real.exp (-((n : ℝ) / d) * z)) := by
  intro _ x y z _ _ hz
  simp only [expPolyTM]
  rw [evalP_expPoly]
  exact expPoly_err sc n d hsc hd hnd z hz

theorem expPolyx_contains (sc : Int) (n d : Nat) (hsc : 0 < sc) (hd : 0 < d) (hnd : n ≤ d) :
    Contains one (expPolyTMx sc n d) (fun x _ _ => (sc : ℝ) / one * Real.exp (-((n : ℝ) / d) * x)) := by
  intro _ x y z hx _ _
  simp only [expPolyTMx]
  rw [evalP_expPolyx]
  exact expPoly_err sc n d hsc hd hnd x hx

/-! ## The `g1` series -/

noncomputable def g1Poly (u : ℝ) : ℝ := 1 + u / 2 + u ^ 2 / 3 + u ^ 3 / 4 + u ^ 4 / 5 + u ^ 5 / 6 + u ^ 6 / 7

theorem g1_series_err {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : |g1 u - (1 - u) * g1Poly u| ≤ u ^ 7 := by
  rcases h0.eq_or_lt with h | h
  · subst h; simp [g1, g1Poly]
  have hu1 : |u| < 1 := by rw [abs_of_pos h]; exact h1
  have hb := Real.abs_log_sub_add_sum_range_le hu1 7
  rw [abs_of_pos h] at hb
  have hs : ∑ i ∈ Finset.range 7, u ^ (i + 1) / ((i : ℝ) + 1) = u * g1Poly u := by
    simp [Finset.sum_range_succ, g1Poly]; try ring
  rw [hs] at hb
  have hne : u ≠ 0 := h.ne'
  have e : g1 u - (1 - u) * g1Poly u = -((1 - u) / u) * (u * g1Poly u + Real.log (1 - u)) := by
    unfold g1; rw [if_neg hne]; field_simp; ring
  rw [e, abs_mul, abs_neg, abs_of_pos (div_pos (by linarith) h)]
  have h1u : 0 < 1 - u := by linarith
  calc (1 - u) / u * |u * g1Poly u + Real.log (1 - u)| ≤ (1 - u) / u * (u ^ (7 + 1) / (1 - u)) :=
        mul_le_mul_of_nonneg_left hb (div_pos h1u h).le
    _ = u ^ 7 := by field_simp <;> ring

theorem natdiv_err (j : ℕ) : |1 / ((j : ℝ) + 1) - (((one / (j + 1) : ℕ) : ℤ) : ℝ) / one| ≤ (1 : ℕ) / one := by
  have hJ : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hA := CKLaneR2.Cell.hone'
  set C : ℝ := ((one / (j + 1) : ℕ) : ℝ) with hC
  have hc : C * ((j : ℝ) + 1) ≤ one := by
    have : (one / (j + 1)) * (j + 1) ≤ one := Nat.div_mul_le_self one (j + 1)
    rw [hC]; exact_mod_cast this
  have hc2 : (one : ℝ) < C * ((j : ℝ) + 1) + ((j : ℝ) + 1) := by
    have h := @Nat.lt_div_mul_add one (j + 1) (Nat.succ_pos j)
    rw [hC]; exact_mod_cast h
  rw [Int.cast_natCast, ← hC, Nat.cast_one]
  have e : 1 / ((j : ℝ) + 1) - C / one = ((one : ℝ) - C * ((j : ℝ) + 1)) / ((one : ℝ) * ((j : ℝ) + 1)) := by
    field_simp
  have hpos : (0 : ℝ) < (one : ℝ) * ((j : ℝ) + 1) := mul_pos hA hJ
  have h0 : 0 ≤ ((one : ℝ) - C * ((j : ℝ) + 1)) / ((one : ℝ) * ((j : ℝ) + 1)) :=
    div_nonneg (by linarith) hpos.le
  rw [e, abs_of_nonneg h0, div_le_div_iff₀ hpos hA]
  nlinarith

theorem g1Step_contains {U S : TM} {uf sf : ℝ → ℝ → ℝ → ℝ} (hU : Contains one U uf) (hS : Contains one S sf)
    (j : ℕ) :
    Contains one (g1Step U S ((one / (j + 1) : ℕ) : Int)) (fun x y z => uf x y z * sf x y z + 1 / ((j : ℝ) + 1)) := by
  have hA := Contains.addc (C_mul hU hS) ((one / (j + 1) : ℕ) : Int)
  have hP := Contains.perturb hA 1 (fun x y z _ _ _ => by
    have := natdiv_err j
    rw [show uf x y z * sf x y z + 1 / ((j : ℝ) + 1)
        - (uf x y z * sf x y z + (((one / (j + 1) : ℕ) : ℤ) : ℝ) / one)
        = 1 / ((j : ℝ) + 1) - (((one / (j + 1) : ℕ) : ℤ) : ℝ) / one by ring]
    exact this)
  exact hP

end CKLaneR2.Tail

end


