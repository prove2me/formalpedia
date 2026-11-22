-- Prove2me | Definitions.Def_GirvingAKS_ZigZag_RVWInequality
-- name    : GirvingAKS_ZigZag_RVWInequality
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:24.028304+00:00
-- url     : https://prove2.me/theorems/2cea1683-91e7-4b95-8c1e-c166f9b7202f
-- title:
--   AKS sorting networks (Seiferas port) — RVW Quadratic Inequality
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/ZigZag/RVWInequality.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** The core scalar inequality needed for the RVW operator norm bound. This is a pure polynomial inequality with no graph or operator theory imports.
--
--   **`rvw_reduced_ineq` (V1'):** The core inequality in 4 variables (α, wh, zh, a). Proved by treating V1' as a quadratic in `a` and analyzing by case on the vertex location relative to [0,1].
--
--   **`rvw_cleared_ineq`:** The cleared polynomial form. Proved from `rvw_reduced_ineq` via concavity reduction + boundary reparameterization.
--
--   **`rvw_quadratic_ineq`:** The original form with spectral gap parameters. Proved from `rvw_cleared_ineq` by clearing denominators and using `p·X ≤ |p|·|X|`.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/ZigZag/RVWInequality.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/ZigZag/RVWInequality.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # RVW Quadratic Inequality

  The core scalar inequality needed for the RVW operator norm bound.
  This is a pure polynomial inequality with no graph or operator theory imports.

  ## Structure

  **`rvw_reduced_ineq` (V1'):** The core inequality in 4 variables (α, wh, zh, a).
  Proved by treating V1' as a quadratic in `a` and analyzing by case on the vertex
  location relative to [0,1].

  **`rvw_cleared_ineq`:** The cleared polynomial form. Proved from `rvw_reduced_ineq`
  via concavity reduction + boundary reparameterization.

  **`rvw_quadratic_ineq`:** The original form with spectral gap parameters.
  Proved from `rvw_cleared_ineq` by clearing denominators and using `p·X ≤ |p|·|X|`.
-/


section


/-! **Quadratic Helpers** -/

private lemma quad_nonneg_of_vertex_ge_one (c₂ c₁ c₀ a : ℝ)
    (hc₂ : 0 ≤ c₂) (ha_hi : a ≤ 1)
    (hf1 : 0 ≤ c₂ + c₁ + c₀)
    (hvertex : c₁ + 2 * c₂ ≤ 0) :
    0 ≤ c₂ * a ^ 2 + c₁ * a + c₀ := by
  nlinarith [mul_nonneg hc₂ (sq_nonneg (a - 1)),
    show 0 ≤ (1 - a) * (-(2 * c₂ + c₁)) from mul_nonneg (by linarith) (by linarith),
    show c₂ * a ^ 2 + c₁ * a + c₀ =
      (c₂ + c₁ + c₀) + (a - 1) * (2 * c₂ + c₁) + c₂ * (a - 1) ^ 2 from by ring]

private lemma quad_nonneg_of_vertex_le_zero (c₂ c₁ c₀ a : ℝ)
    (hc₂ : 0 ≤ c₂) (ha_lo : 0 ≤ a)
    (hf0 : 0 ≤ c₀) (hvertex : 0 ≤ c₁) :
    0 ≤ c₂ * a ^ 2 + c₁ * a + c₀ := by
  nlinarith [mul_nonneg ha_lo hvertex, mul_nonneg hc₂ (sq_nonneg a)]

private lemma quad_nonneg_of_disc_nonpos (c₂ c₁ c₀ a : ℝ)
    (hc₂ : 0 ≤ c₂) (hf0 : 0 ≤ c₀)
    (hdisc : c₁ ^ 2 ≤ 4 * c₂ * c₀) :
    0 ≤ c₂ * a ^ 2 + c₁ * a + c₀ := by
  by_cases hc₂0 : c₂ = 0
  · have hc₁ : c₁ = 0 := by nlinarith [sq_nonneg c₁]
    nlinarith [show c₂ * a ^ 2 + c₁ * a + c₀ = c₀ from by rw [hc₂0, hc₁]; ring]
  · nlinarith [sq_nonneg (2 * c₂ * a + c₁),
      show 4 * c₂ * (c₂ * a ^ 2 + c₁ * a + c₀) =
        (2 * c₂ * a + c₁) ^ 2 + (4 * c₂ * c₀ - c₁ ^ 2) from by ring,
      show 0 < c₂ from lt_of_le_of_ne hc₂ (Ne.symm hc₂0)]

/-! **The Reduced Inequality (V1')** -/

set_option maxHeartbeats 800000 in
theorem rvw_reduced_ineq (α wh zh a : ℝ)
    (hα_lo : 0 ≤ α) (hα_hi : α ≤ 1)
    (ha_lo : 0 ≤ a) (ha_hi : a ≤ 1)
    (h_constraint : α * zh ^ 2 + (1 - α) * wh ^ 2 ≤ 2 * α * (1 - α)) :
    let ph := α - wh ^ 2
    let Xh := 1 - (wh - zh) ^ 2
    α * (1 - α) + (1 - a) * ph * Xh ≥ a * α * (1 - a * α) * Xh ^ 2 := by
  set t := wh - zh
  set Xh := 1 - t ^ 2
  set inner := α * t ^ 2 - 2 * α + wh ^ 2
  -- Rewrite as quadratic in a: c₂a²+c₁a+c₀ ≥ 0
  suffices h : 0 ≤ (α ^ 2 * Xh ^ 2) * a ^ 2 + (Xh * inner) * a +
      (α * (1 - α) + (α - wh ^ 2) * Xh) by
    nlinarith [show α * (1 - α) + (1 - a) * (α - wh ^ 2) * Xh -
      a * α * (1 - a * α) * Xh ^ 2 = (α ^ 2 * Xh ^ 2) * a ^ 2 +
      (Xh * inner) * a + (α * (1 - α) + (α - wh ^ 2) * Xh) from by
      simp only [Xh, inner]; ring]
  -- Constraint in quadratic form: (wh-αt)² ≤ α(1-α)(2-t²)
  have hcr : (wh - α * t) ^ 2 ≤ α * (1 - α) * (2 - t ^ 2) := by
    nlinarith [show (wh - α * t) ^ 2 - α * (1 - α) * (2 - t ^ 2) =
      α * zh ^ 2 + (1 - α) * wh ^ 2 - 2 * α * (1 - α) from by simp only [t]; ring]
  -- c₀ ≥ 0: identity c₀ = slack + (α-wh·t)²
  have hc₀ : 0 ≤ α * (1 - α) + (α - wh ^ 2) * Xh := by
    nlinarith [sq_nonneg (α - wh * t), show α * (1 - α) + (α - wh ^ 2) * Xh =
      (2 * α * (1 - α) - α * zh ^ 2 - (1 - α) * wh ^ 2) + (α - wh * t) ^ 2 from by
      simp only [Xh, t]; ring]
  -- c₂ ≥ 0
  have hc₂ : 0 ≤ α ^ 2 * Xh ^ 2 := mul_nonneg (sq_nonneg α) (sq_nonneg Xh)
  -- Case α = 0: wh = 0, everything vanishes
  by_cases hα0 : α = 0
  · nlinarith [show (α ^ 2 * Xh ^ 2) * a ^ 2 + (Xh * inner) * a +
      (α * (1 - α) + (α - wh ^ 2) * Xh) = 0 from by
      have : wh = 0 := by
        have : wh ^ 2 ≤ 0 := by nlinarith
        exact mul_self_eq_zero.mp (by nlinarith [sq_nonneg wh,
          show wh * wh = wh ^ 2 from by ring])
      simp only [inner, Xh, t, hα0, this]; ring]
  -- Case α = 1: zh = 0, f(a) = (1-a)²(1-wh²)²
  by_cases hα1 : α = 1
  · nlinarith [mul_nonneg (sq_nonneg (1 - a)) (sq_nonneg (1 - wh ^ 2)),
      show (α ^ 2 * Xh ^ 2) * a ^ 2 + (Xh * inner) * a +
        (α * (1 - α) + (α - wh ^ 2) * Xh) = (1 - a) ^ 2 * (1 - wh ^ 2) ^ 2 from by
        have : zh = 0 := by
          have : zh ^ 2 ≤ 0 := by nlinarith
          exact mul_self_eq_zero.mp (by nlinarith [sq_nonneg zh,
            show zh * zh = zh ^ 2 from by ring])
        simp only [Xh, inner, t, hα1, this]; ring]
  -- 0 < α < 1
  have hα_pos : 0 < α := lt_of_le_of_ne hα_lo (Ne.symm hα0)
  have h1α_pos : 0 < 1 - α := by linarith [lt_of_le_of_ne hα_hi hα1]
  -- t² ≤ 2 (from constraint: (wh-αt)²≥0 and α(1-α)>0 force 2-t²≥0)
  have ht2 : t ^ 2 ≤ 2 := by
    by_contra h; push_neg at h
    have h1 : 0 < α * (1 - α) := mul_pos hα_pos h1α_pos
    linarith [sq_nonneg (wh - α * t), mul_neg_of_pos_of_neg h1 (by linarith : 2 - t ^ 2 < 0)]
  -- f(1) ≥ 0: identity f(1) = α(1-α)t²(2-t²)
  have hf1 : 0 ≤ (α ^ 2 * Xh ^ 2) + (Xh * inner) +
      (α * (1 - α) + (α - wh ^ 2) * Xh) := by
    nlinarith [mul_nonneg (mul_nonneg hα_lo h1α_pos.le) (sq_nonneg t),
      show (α ^ 2 * Xh ^ 2) + (Xh * inner) + (α * (1 - α) + (α - wh ^ 2) * Xh) =
        α * (1 - α) * t ^ 2 * (2 - t ^ 2) from by simp only [Xh, inner]; ring]
  -- Case Xh = 0: f(a) = α(1-α) ≥ 0
  by_cases hXh : Xh = 0
  · nlinarith [mul_nonneg hα_lo h1α_pos.le,
      show (α ^ 2 * Xh ^ 2) * a ^ 2 + (Xh * inner) * a +
        (α * (1 - α) + (α - wh ^ 2) * Xh) = α * (1 - α) from by rw [hXh]; ring]
  -- Case factor2 ≥ 0: disc ≤ 0
  by_cases hf2 : 0 ≤ (wh + α * t) ^ 2 - α * (1 - α) * (2 - t ^ 2)
  · apply quad_nonneg_of_disc_nonpos _ _ _ a hc₂ hc₀
    -- disc = Xh²·(-slack)·factor2, product of (nonneg)·(nonpos)·(nonneg) ≤ 0
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg Xh) hf2)
        (show 0 ≤ 2 * α * (1 - α) - α * zh ^ 2 - (1 - α) * wh ^ 2 from by linarith),
      show (Xh * inner) ^ 2 - 4 * (α ^ 2 * Xh ^ 2) *
        (α * (1 - α) + (α - wh ^ 2) * Xh) +
        Xh ^ 2 * ((wh + α * t) ^ 2 - α * (1 - α) * (2 - t ^ 2)) *
        (2 * α * (1 - α) - α * zh ^ 2 - (1 - α) * wh ^ 2) = 0 from by
        simp only [Xh, inner, t]; ring]
  · push_neg at hf2
    -- factor2 < 0: averaging gives wh²+α²t² ≤ α(1-α)(2-t²)
    have hsum : wh ^ 2 + α ^ 2 * t ^ 2 ≤ α * (1 - α) * (2 - t ^ 2) := by
      nlinarith [show (wh - α * t) ^ 2 + (wh + α * t) ^ 2 =
        2 * wh ^ 2 + 2 * α ^ 2 * t ^ 2 from by ring,
        show 2 * (α * (1 - α) * (2 - t ^ 2)) = 2 * α * (1 - α) * (2 - t ^ 2) from by ring]
    by_cases hXh_pos : 0 < Xh
    · -- Xh > 0, vertex ≥ 1: show c₁+2c₂ ≤ 0
      apply quad_nonneg_of_vertex_ge_one _ _ _ a hc₂ ha_hi hf1
      -- c₁+2c₂ = Xh·(inner+2α²Xh); Xh>0 so need inner+2α²Xh ≤ 0
      have hv : inner + 2 * α ^ 2 * Xh ≤ 0 := by
        nlinarith [sq_nonneg (α * t),
          show inner + 2 * α ^ 2 * Xh + 2 * α ^ 2 * t ^ 2 =
            (wh ^ 2 + α ^ 2 * t ^ 2) + α * (1 - α) * t ^ 2 -
            2 * α * (1 - α) from by simp only [inner, Xh]; ring,
          show α * (1 - α) * (2 - t ^ 2) + α * (1 - α) * t ^ 2 -
            2 * α * (1 - α) = 0 from by ring]
      nlinarith [show Xh * inner + 2 * (α ^ 2 * Xh ^ 2) =
        Xh * (inner + 2 * α ^ 2 * Xh) from by ring,
        mul_nonneg hXh_pos.le (show 0 ≤ -(inner + 2 * α ^ 2 * Xh) from by linarith)]
    · -- Xh < 0, vertex ≤ 0: show c₁ ≥ 0
      push_neg at hXh_pos
      have hXh_neg : Xh < 0 := lt_of_le_of_ne hXh_pos hXh
      -- inner ≤ -2α² < 0 from averaging
      have hinner_neg : inner < 0 := by
        have hid : inner + 2 * α ^ 2 =
          wh ^ 2 + α ^ 2 * t ^ 2 + α * (1 - α) * t ^ 2 -
          2 * α * (1 - α) := by simp only [inner]; ring
        have hzero : α * (1 - α) * (2 - t ^ 2) + α * (1 - α) * t ^ 2 -
          2 * α * (1 - α) = 0 := by ring
        nlinarith [sq_nonneg α]
      apply quad_nonneg_of_vertex_le_zero _ _ _ a hc₂ ha_lo hc₀
      exact le_of_lt (mul_pos_of_neg_of_neg hXh_neg hinner_neg)

/-! **Concavity Reduction** -/

private lemma concave_nonneg_of_endpoints (α β γ q M : ℝ)
    (hα : α ≤ 0) (hM : 0 < M) (hq_lo : -M ≤ q) (hq_hi : q ≤ M)
    (hfM : α * M ^ 2 + β * M + γ ≥ 0)
    (hfnM : α * M ^ 2 - β * M + γ ≥ 0) :
    α * q ^ 2 + β * q + γ ≥ 0 := by
  have key : (α * q ^ 2 + β * q + γ) * (2 * M) =
    (α * M ^ 2 + β * M + γ) * (M + q) +
    (α * M ^ 2 - β * M + γ) * (M - q) +
    2 * M * α * (q ^ 2 - M ^ 2) := by ring
  have h1 : 0 ≤ (α * M ^ 2 + β * M + γ) * (M + q) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (α * M ^ 2 - β * M + γ) * (M - q) :=
    mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ 2 * M * α * (q ^ 2 - M ^ 2) := by
    nlinarith [sq_nonneg q, sq_nonneg M,
      mul_nonneg (show (0:ℝ) ≤ 2 * M from by linarith)
        (mul_nonneg (show (0:ℝ) ≤ -α from by linarith)
          (show (0:ℝ) ≤ M ^ 2 - q ^ 2 from by nlinarith)),
      show 2 * M * (-α) * (M ^ 2 - q ^ 2) =
        2 * M * α * (q ^ 2 - M ^ 2) from by ring]
  by_contra h_neg
  push_neg at h_neg
  linarith [mul_neg_of_neg_of_pos h_neg (by linarith : (0 : ℝ) < 2 * M)]

/-! **Boundary Reparameterization** -/

private lemma boundary_nonneg_of_reduced
    (a b c p r M : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hcb : c ≤ b)
    (h_unit : a ^ 2 + b ^ 2 = 1)
    (h_refl_u : |p| ≤ a ^ 2) (h_refl_w : |r| ≤ c ^ 2)
    (hM_sq : M ^ 2 = (a ^ 2 - p) * (c ^ 2 - r))
    (hM_nonneg : 0 ≤ M)
    (hF : (a ^ 2 - p) * (c ^ 2 - r) ≤ (a ^ 2 + p) * (c ^ 2 + r))
    (hS_pos : 0 < a ^ 2 + c ^ 2)
    (h_reduced : ∀ (α wh zh a_param : ℝ),
      0 ≤ α → α ≤ 1 → 0 ≤ a_param → a_param ≤ 1 →
      α * zh ^ 2 + (1 - α) * wh ^ 2 ≤ 2 * α * (1 - α) →
      α * (1 - α) + (1 - a_param) * (α - wh ^ 2) * (1 - (wh - zh) ^ 2) ≥
        a_param * α * (1 - a_param * α) * (1 - (wh - zh) ^ 2) ^ 2) :
    a ^ 2 * c ^ 2 + (b ^ 2 - c ^ 2) * p * (p + 2 * M + r) -
      a ^ 2 * b ^ 2 * (p + 2 * M + r) ^ 2 ≥ 0 ∧
    a ^ 2 * c ^ 2 + (b ^ 2 - c ^ 2) * p * (p - 2 * M + r) -
      a ^ 2 * b ^ 2 * (p - 2 * M + r) ^ 2 ≥ 0 := by
  set A := a ^ 2
  set B := b ^ 2
  set C := c ^ 2
  set S := A + C
  have hAp : 0 ≤ A - p := by nlinarith [abs_le.mp h_refl_u]
  have hCr : 0 ≤ C - r := by nlinarith [abs_le.mp h_refl_w]
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hS_sq_pos : (0:ℝ) < S ^ 2 := by positivity
  have hArCp : 0 ≤ A * r + C * p := by nlinarith [hF]
  have h1A : B = 1 - A := by linarith [h_unit]
  have hAp_div : 0 ≤ (A - p) / S := div_nonneg hAp hS_pos.le
  have hCr_div : 0 ≤ (C - r) / S := div_nonneg hCr hS_pos.le
  set wh := Real.sqrt ((A - p) / S)
  set zh := Real.sqrt ((C - r) / S)
  have hwh_sq : wh ^ 2 = (A - p) / S := Real.sq_sqrt hAp_div
  have hzh_sq : zh ^ 2 = (C - r) / S := Real.sq_sqrt hCr_div
  have hwh_nn : 0 ≤ wh := Real.sqrt_nonneg _
  have hzh_nn : 0 ≤ zh := Real.sqrt_nonneg _
  have hwh_zh : wh * zh = M / S := by
    have hsq : (wh * zh) ^ 2 = (M / S) ^ 2 := by
      rw [mul_pow, hwh_sq, hzh_sq, div_pow, hM_sq]; field_simp
    have h1 := congr_arg Real.sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
         abs_of_nonneg (mul_nonneg hwh_nn hzh_nn),
         abs_of_nonneg (div_nonneg hM_nonneg hS_pos.le)] at h1
  have hα_lo : 0 ≤ A / S := div_nonneg (by positivity) hS_pos.le
  have hα_hi : A / S ≤ 1 := by rw [div_le_one hS_pos]; linarith [show 0 ≤ C from sq_nonneg c]
  have hS_lo : 0 ≤ S := hS_pos.le
  have hS_hi : S ≤ 1 := by nlinarith [h_unit, sq_nonneg b, sq_nonneg c, hcb]
  have h_constr : A / S * zh ^ 2 + (1 - A / S) * wh ^ 2 ≤ 2 * (A / S) * (1 - A / S) := by
    rw [hwh_sq, hzh_sq]
    have lhs_eq : A / S * ((C - r) / S) + (1 - A / S) * ((A - p) / S) =
        (A * (C - r) + C * (A - p)) / S ^ 2 := by field_simp; ring
    have rhs_eq : 2 * (A / S) * (1 - A / S) = 2 * A * C / S ^ 2 := by field_simp; ring
    rw [lhs_eq, rhs_eq, div_le_div_iff_of_pos_right hS_sq_pos]
    nlinarith [hArCp]
  have hV1_plus := h_reduced (A / S) wh zh S hα_lo hα_hi hS_lo hS_hi h_constr
  have hV1_minus := h_reduced (A / S) wh (-zh) S hα_lo hα_hi hS_lo hS_hi
    (by simp only [neg_sq]; exact h_constr)
  have hph : A / S - wh ^ 2 = p / S := by rw [hwh_sq]; field_simp; ring
  have hXh_plus : 1 - (wh - zh) ^ 2 = (p + 2 * M + r) / S := by
    have : (wh - zh) ^ 2 = wh ^ 2 - 2 * (wh * zh) + zh ^ 2 := by ring
    rw [this, hwh_sq, hzh_sq, hwh_zh]; field_simp; ring
  have hXh_minus : 1 - (wh - (-zh)) ^ 2 = (p - 2 * M + r) / S := by
    have : (wh - (-zh)) ^ 2 = wh ^ 2 + 2 * (wh * zh) + zh ^ 2 := by ring
    rw [this, hwh_sq, hzh_sq, hwh_zh]; field_simp; ring
  constructor
  · have heq : A * C + (B - C) * p * (p + 2 * M + r) - A * B * (p + 2 * M + r) ^ 2 =
        S ^ 2 * (A / S * (1 - A / S) + (1 - S) * (A / S - wh ^ 2) * (1 - (wh - zh) ^ 2) -
        S * (A / S) * (1 - S * (A / S)) * (1 - (wh - zh) ^ 2) ^ 2) := by
      rw [h1A, hph]; simp only [hXh_plus]; field_simp; ring
    rw [heq]; exact mul_nonneg (sq_nonneg S) (by linarith [hV1_plus])
  · have heq : A * C + (B - C) * p * (p - 2 * M + r) - A * B * (p - 2 * M + r) ^ 2 =
        S ^ 2 * (A / S * (1 - A / S) + (1 - S) * (A / S - wh ^ 2) *
        (1 - (wh - (-zh)) ^ 2) -
        S * (A / S) * (1 - S * (A / S)) * (1 - (wh - (-zh)) ^ 2) ^ 2) := by
      rw [h1A, hph]; simp only [hXh_minus]; field_simp; ring
    rw [heq]; exact mul_nonneg (sq_nonneg S) (by linarith [hV1_minus])

/-! **The Cleared Inequality** -/

theorem rvw_cleared_ineq
    (a b c p q r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hcb : c ≤ b)
    (h_unit : a ^ 2 + b ^ 2 = 1)
    (h_refl_u : |p| ≤ a ^ 2) (h_refl_w : |r| ≤ c ^ 2)
    (h_cs_plus : q ^ 2 ≤ (a ^ 2 + p) * (c ^ 2 + r))
    (h_cs_minus : q ^ 2 ≤ (a ^ 2 - p) * (c ^ 2 - r)) :
    a ^ 2 * c ^ 2 + (b ^ 2 - c ^ 2) * p * (p + 2 * q + r) -
      a ^ 2 * b ^ 2 * (p + 2 * q + r) ^ 2 ≥ 0 := by
  set A := a ^ 2
  set B := b ^ 2
  set C := c ^ 2
  by_cases hc0 : c = 0
  · have hC : C = 0 := by simp [C, hc0]
    have hr : r = 0 := abs_nonpos_iff.mp (by linarith [h_refl_w, hC] : |r| ≤ 0)
    have hq0 : q = 0 := by
      have h : (A - p) * (C - r) = 0 := by rw [hC, hr]; ring
      have h1 : q ^ 2 ≤ 0 := by linarith [h_cs_minus]
      exact sq_eq_zero_iff.mp (le_antisymm h1 (sq_nonneg q))
    have h1A : B = 1 - A := by linarith [h_unit]
    have heq : A * C + (B - C) * p * (p + 2 * q + r) - A * B * (p + 2 * q + r) ^ 2 =
        B ^ 2 * p ^ 2 := by rw [hC, hr, hq0, h1A]; ring
    linarith [heq, mul_nonneg (sq_nonneg B) (sq_nonneg p)]
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    suffices h_wlog : ∀ (p' q' r' : ℝ),
        |p'| ≤ A → |r'| ≤ C →
        q' ^ 2 ≤ (A + p') * (C + r') →
        q' ^ 2 ≤ (A - p') * (C - r') →
        (A - p') * (C - r') ≤ (A + p') * (C + r') →
        A * C + (B - C) * p' * (p' + 2 * q' + r') -
          A * B * (p' + 2 * q' + r') ^ 2 ≥ 0 by
      by_cases hF : (A - p) * (C - r) ≤ (A + p) * (C + r)
      · exact h_wlog p q r h_refl_u h_refl_w h_cs_plus h_cs_minus hF
      · push_neg at hF
        have h_neg := h_wlog (-p) (-q) (-r)
          (by rwa [abs_neg]) (by rwa [abs_neg])
          (by nlinarith [h_cs_minus]) (by nlinarith [h_cs_plus])
          (by nlinarith)
        linarith [show A * C + (B - C) * (-p) * (-p + 2 * (-q) + -r) -
          A * B * (-p + 2 * (-q) + -r) ^ 2 =
          A * C + (B - C) * p * (p + 2 * q + r) -
          A * B * (p + 2 * q + r) ^ 2 from by ring]
    intro p' q' r' hp' hr' hcs_plus' hcs_minus' hF'
    set s := p' + r'
    have hF2_nonneg : 0 ≤ (A - p') * (C - r') := by
      have := abs_le.mp hp'; have := abs_le.mp hr'; nlinarith
    set M := Real.sqrt ((A - p') * (C - r'))
    have hM_nonneg : 0 ≤ M := Real.sqrt_nonneg _
    have hM_sq : M ^ 2 = (A - p') * (C - r') := Real.sq_sqrt hF2_nonneg
    have hq_le_M : q' ^ 2 ≤ M ^ 2 := by rw [hM_sq]; exact hcs_minus'
    have hq_abs_le : |q'| ≤ M := by
      have h := Real.sqrt_le_sqrt hq_le_M
      rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hM_nonneg] at h
    have hq_lo : -M ≤ q' := neg_le_of_abs_le hq_abs_le
    have hq_hi : q' ≤ M := abs_le.mp hq_abs_le |>.2
    by_cases hM0 : M = 0
    · have hq'0 : q' = 0 := by nlinarith [sq_nonneg q']
      rw [hq'0]
      have := boundary_nonneg_of_reduced a b c p' r' 0
        ha hb hc hcb h_unit hp' hr'
        (by have := hM_sq; rw [hM0] at this; simpa using this)
        (le_refl 0) hF'
        (by positivity)
        (fun α wh zh a_param hα₁ hα₂ ha₁ ha₂ h5 ↦
          rvw_reduced_ineq α wh zh a_param hα₁ hα₂ ha₁ ha₂ h5)
      simp at this; linarith [this]
    · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM0)
      have hS_pos : 0 < A + C := by positivity
      have h_bdry := boundary_nonneg_of_reduced a b c p' r' M
        ha hb hc hcb h_unit hp' hr' hM_sq hM_nonneg hF' hS_pos
        (fun α wh zh a_param hα₁ hα₂ ha₁ ha₂ h5 ↦
          rvw_reduced_ineq α wh zh a_param hα₁ hα₂ ha₁ ha₂ h5)
      obtain ⟨hGM, hGnM⟩ := h_bdry
      have h_quad_form : ∀ t : ℝ,
          A * C + (B - C) * p' * (p' + 2 * t + r') -
            A * B * (p' + 2 * t + r') ^ 2 =
          (-4 * A * B) * t ^ 2 + (2 * (B - C) * p' - 4 * A * B * s) * t +
          (A * C + (B - C) * p' * s - A * B * s ^ 2) := by
        intro t; simp [s]; ring
      rw [h_quad_form]
      apply concave_nonneg_of_endpoints (-4 * A * B)
        (2 * (B - C) * p' - 4 * A * B * s)
        (A * C + (B - C) * p' * s - A * B * s ^ 2) q' M
      · nlinarith [sq_nonneg a, sq_nonneg b]
      · exact hM_pos
      · exact hq_lo
      · exact hq_hi
      · linarith [h_quad_form M]
      · have := h_quad_form (-M)
        simp only [neg_sq] at this
        linarith [show 2 * (B - C) * p' * (-M) =
                    -(2 * (B - C) * p' * M) from by ring,
                  show 4 * A * B * s * (-M) =
                    -(4 * A * B * s * M) from by ring,
                  show A * C + (B - C) * p' * (p' + 2 * (-M) + r') -
                    A * B * (p' + 2 * (-M) + r') ^ 2 =
                    A * C + (B - C) * p' * (p' - 2 * M + r') -
                    A * B * (p' - 2 * M + r') ^ 2 from by ring]

/-! **The Division Form** -/

theorem rvw_quadratic_ineq
    (a b c p q r : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hcb : c ≤ b)
    (h_unit : a ^ 2 + b ^ 2 = 1)
    (h_refl_u : |p| ≤ a ^ 2) (h_refl_w : |r| ≤ c ^ 2)
    (h_cs_plus : q ^ 2 ≤ (a ^ 2 + p) * (c ^ 2 + r))
    (h_cs_minus : q ^ 2 ≤ (a ^ 2 - p) * (c ^ 2 - r)) :
    (p + 2 * q + r) ^ 2 ≤
      (1 - (c / b) ^ 2) * (|p| / a ^ 2) * |p + 2 * q + r| + (c / b) ^ 2 := by
  set X := p + 2 * q + r
  have hab2 : (0 : ℝ) < a ^ 2 * b ^ 2 := by positivity
  suffices h : a ^ 2 * b ^ 2 * X ^ 2 ≤
      (b ^ 2 - c ^ 2) * |p| * |X| + a ^ 2 * c ^ 2 by
    have h1 : X ^ 2 ≤ ((b ^ 2 - c ^ 2) * |p| * |X| + a ^ 2 * c ^ 2) /
        (a ^ 2 * b ^ 2) := by
      rw [le_div_iff₀ hab2]; nlinarith
    calc X ^ 2
        ≤ ((b ^ 2 - c ^ 2) * |p| * |X| + a ^ 2 * c ^ 2) /
            (a ^ 2 * b ^ 2) := h1
      _ = (1 - (c / b) ^ 2) * (|p| / a ^ 2) * |X| + (c / b) ^ 2 := by
            rw [div_pow]; field_simp
  have hb2c2 : c ^ 2 ≤ b ^ 2 := by nlinarith [sq_nonneg c, sq_nonneg b]
  suffices h_main : a ^ 2 * c ^ 2 + (b ^ 2 - c ^ 2) * p * X -
      a ^ 2 * b ^ 2 * X ^ 2 ≥ 0 by
    have hbc : 0 ≤ b ^ 2 - c ^ 2 := by linarith
    have hpX : p * X ≤ |p| * |X| := by rw [← abs_mul]; exact le_abs_self _
    have := mul_le_mul_of_nonneg_left hpX hbc
    nlinarith
  exact rvw_cleared_ineq a b c p q r ha hb hc hcb h_unit h_refl_u h_refl_w
    h_cs_plus h_cs_minus

end


