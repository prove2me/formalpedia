-- Prove2me | Definitions.Def_TateCurve_XMultSeparation
-- name    : TateCurve_XMultSeparation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/bce0032e-8047-507e-ab1a-d46aafe46b79
-- title:
--   Separation of Tate-curve x-coordinates; unconditional SymAddHyps
-- statement:
--   Throughout, $K$ is a complete, nontrivially normed ultrametric field of characteristic zero and $q,u,v \in K$. The project notions used are: `OffLattice q w`, meaning $q^n w \neq 1$ for every $n \in \mathbb{Z}$; `AddParams q u v`, the conjunction $q \neq 0$, $u \neq 0$, $v \neq 0$ together with `OffLattice q` for each of $u$, $v$, $uv$ and $uv^{-1}$; the symmetric-function numerators $\mathrm{symSumNum}\,q\,x_1\,x_2 = 2x_1x_2(x_1+x_2) + x_1x_2 + 2a_4(q)(x_1+x_2) + 4a_6(q)$ and $\mathrm{symProdNum}\,q\,x_1\,x_2 = (x_1x_2)^2 - 2a_4(q)(x_1x_2) - 4a_6(q)(x_1+x_2) - a_6(q) + a_4(q)^2$; and `SymAddHyps q`, the structure whose fields are the sum, product and duplication identities for `pointX` along admissible pairs.
--
--   The auxiliary lemmas record elementary inequalities between real norms, the dichotomy that for $q \neq 0$ with $\|q\| < 1$ each $\|q^n\|$ ($n \in \mathbb{Z}$) is either $\le \|q\|$ or $\ge 1$, that $\|q\| < \|x\| < 1$ forces `OffLattice q x`, and that under `AddParams q u v` neither $q^a u = q^b v$ nor $(q^a u)(q^b v) = 1$ can hold for integers $a,b$.
--
--   `pointX_ne_of_addParams_of_psiTwo` assumes $q \neq 0$, $\|q\| < 1$, the existence of $w$ with $\|q\| < \|w\|^2$ and $\|w\| < 1$, the two identities
--   $$(X(uv) \pm X(uv^{-1}))(X(u)-X(v))^2 = \mathrm{symSumNum}\ \text{resp.}\ -\big(2Y(u)+X(u)\big)\big(2Y(v)+X(v)\big)$$
--   for all admissible pairs, an `AddParams q u v`, and $2Y(u)+X(u) = 0 = 2Y(v)+X(v)$; it concludes $X(u) \neq X(v)$. The proof normalises $u,v$ by powers of $q$ into the annulus $\|q\| < \|\cdot\| \le 1$, splits on the position of $\|q^k u\|\,\|q^m v\|$ relative to $\|q\|$, and cites `eq_or_mul_eq_one_of_pointX_eq`; on the locus $\|q^k u\| = \|q^m v\| = \|q\|^{1/2}$ the auxiliary $w$ is used to transport the equality into the admissible window.
--
--   `symAdd_prod_of_sum_diff_forall_of_exists` deduces, from the same data, the product identity for every admissible pair, and `symAddHyps_of_sum_diff_of_exists` packages this into `SymAddHyps q` via `symAddHyps_of_sum_prod`. Finally `symAddHyps_of_sum_diff_of_isAlgClosed` removes the hypothesis on $w$ when $K$ is algebraically closed, by taking a fourth root of $q$.
--
--   **Relation to Mathlib.** Mathlib has no Tate parametrisation; `OffLattice`, `AddParams`, `symSumNum`, `symProdNum`, `SymAddHyps` and the coordinate functions `pointX`, `pointY` are the project's own notions. The Mathlib input here is the ultrametric normed-field API and, in the last theorem, the existence of $n$-th roots in an algebraically closed field.
--
--   **Where it is used.** `SymAddHyps q` is the hypothesis feeding the ladder that identifies `pointX q (u^j)` with the $x$-coordinates of the multiples $j \cdot P$ of the Tate point attached to $u$, and hence the analysis of $p$-torsion on a curve with multiplicative reduction. These theorems make that bundle available from the sum and difference identities alone, with no residual separation assumption when the base field is algebraically closed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_XMultSeparation.lean

import Mathlib
import Definitions.Def_TateCurve_XMultDistinctRouteB

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v : K}

section Helpers

private lemma lt_of_mul_self_lt_mul_self {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a * a < b * b) : a < b := by
  nlinarith

private lemma lt_mul_inv_of_mul_lt {a b c : ℝ} (hb : 0 < b) (h : c * b < a) : c < a * b⁻¹ := by
  have h2 := mul_lt_mul_of_pos_right h (inv_pos.mpr hb)
  rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), mul_one] at h2

private lemma mul_inv_le_one_of_le {a b : ℝ} (hb : 0 < b) (h : a ≤ b) : a * b⁻¹ ≤ 1 := by
  have h2 := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hb.le)
  rwa [mul_inv_cancel₀ (ne_of_gt hb)] at h2

private lemma mul_inv_lt_one_of_lt {a b : ℝ} (hb : 0 < b) (h : a < b) : a * b⁻¹ < 1 := by
  have h2 := mul_lt_mul_of_pos_right h (inv_pos.mpr hb)
  rwa [mul_inv_cancel₀ (ne_of_gt hb)] at h2

private lemma norm_zpow_le_or_one_le (hq0 : q ≠ 0) (hqR : ‖q‖ < 1) (n : ℤ) :
    ‖(q ^ n : K)‖ ≤ ‖q‖ ∨ (1 : ℝ) ≤ ‖(q ^ n : K)‖ := by
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  by_cases hn : 1 ≤ n
  ·
    left
    obtain ⟨a, ha⟩ : ∃ a : ℕ, n = (a : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    have hsplit : (q : K) ^ n = q ^ (a : ℕ) * q := by
      rw [ha, zpow_add₀ hq0, zpow_one, zpow_natCast]
    rw [hsplit, norm_mul, norm_pow]
    calc ‖q‖ ^ a * ‖q‖ ≤ 1 * ‖q‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hqpos.le hqR.le) hqpos.le
      _ = ‖q‖ := one_mul _
  ·
    right
    obtain ⟨a, ha⟩ : ∃ a : ℕ, n = -(a : ℤ) := ⟨(-n).toNat, by omega⟩
    have hpow : (q : K) ^ n = (q ^ (a : ℕ))⁻¹ := by
      rw [ha, zpow_neg, zpow_natCast]
    have hpos : (0 : ℝ) < ‖q‖ ^ a := pow_pos hqpos a
    have hle : ‖q‖ ^ a ≤ 1 := pow_le_one₀ hqpos.le hqR.le
    rw [hpow, norm_inv, norm_pow]
    calc (1 : ℝ) = ‖q‖ ^ a * (‖q‖ ^ a)⁻¹ := (mul_inv_cancel₀ (ne_of_gt hpos)).symm
      _ ≤ 1 * (‖q‖ ^ a)⁻¹ :=
          mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr hpos.le)
      _ = (‖q‖ ^ a)⁻¹ := one_mul _

lemma offLattice_of_norm_Ioo (hq0 : q ≠ 0) (hqR : ‖q‖ < 1) {x : K}
    (h1 : ‖q‖ < ‖x‖) (h2 : ‖x‖ < 1) : OffLattice q x := by
  intro n hn

  have hx : x = (q ^ n)⁻¹ := eq_inv_of_mul_eq_one_right hn
  have hxnorm : ‖x‖ = ‖(q ^ (-n) : K)‖ := by rw [hx, ← zpow_neg]
  rcases norm_zpow_le_or_one_le hq0 hqR (-n) with hle | hge
  · rw [hxnorm] at h1; linarith
  · rw [hxnorm] at h2; linarith

private lemma AddParams.contra_div (h : AddParams q u v) {a b : ℤ}
    (heq : q ^ a * u = q ^ b * v) : False := by
  have hq0 := h.q_ne_zero
  apply h.offLattice_div (a - b)
  have hu : u = q ^ (-a) * (q ^ b * v) := by
    rw [← heq, ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul]
  rw [hu]
  calc q ^ (a - b) * (q ^ (-a) * (q ^ b * v) * v⁻¹)
      = (q ^ (a - b) * q ^ (-a) * q ^ b) * (v * v⁻¹) := by ring
    _ = q ^ (a - b + -a + b) * 1 := by
        rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, mul_inv_cancel₀ h.v_ne_zero]
    _ = 1 := by
        rw [show a - b + -a + b = 0 by omega, zpow_zero, one_mul]

private lemma AddParams.contra_mul (h : AddParams q u v) {a b : ℤ}
    (heq : (q ^ a * u) * (q ^ b * v) = 1) : False := by
  have hq0 := h.q_ne_zero
  apply h.offLattice_mul (a + b)
  calc q ^ (a + b) * (u * v) = (q ^ a * u) * (q ^ b * v) := by
        rw [zpow_add₀ hq0]; ring
    _ = 1 := heq

end Helpers

section Windowed

private lemma contra_of_window (hq : ‖q‖₊ < 1) (h : AddParams q u v) {k m : ℤ}
    (hk2 : ‖q ^ k * u‖ ≤ 1) (hm2 : ‖q ^ m * v‖ ≤ 1)
    (hX : pointX q u = pointX q v)
    (hA : ‖q‖ < ‖q ^ k * u‖ * ‖q ^ m * v‖) : False := by
  have hq0 := h.q_ne_zero
  have hu'0 : q ^ k * u ≠ 0 := mul_ne_zero (zpow_ne_zero k hq0) h.u_ne_zero
  have hv'0 : q ^ m * v ≠ 0 := mul_ne_zero (zpow_ne_zero m hq0) h.v_ne_zero
  have hu'lat : OffLattice q (q ^ k * u) := h.offLattice_u.zpow_mul hq0 k
  have hv'lat : OffLattice q (q ^ m * v) := h.offLattice_v.zpow_mul hq0 m
  have hX' : pointX q (q ^ k * u) = pointX q (q ^ m * v) := by
    rw [pointX_zpow_mul hq0 k, pointX_zpow_mul hq0 m, hX]
  have hwin : ‖q‖ < ‖(q ^ k * u) * (q ^ m * v)‖ := by rwa [norm_mul]
  rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hu'0 hv'0 hu'lat hv'lat hk2 hm2 hwin hX' with
    hcase | hcase
  · exact h.contra_div hcase
  · exact h.contra_mul hcase

private lemma contra_of_mul_lt (hq : ‖q‖₊ < 1) (h : AddParams q u v) {k m : ℤ}
    (hk1 : ‖q‖ < ‖q ^ k * u‖) (hm1 : ‖q‖ < ‖q ^ m * v‖)
    (hX : pointX q u = pointX q v)
    (hC : ‖q ^ k * u‖ * ‖q ^ m * v‖ < ‖q‖) : False := by
  have hq0 := h.q_ne_zero
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu'0 : q ^ k * u ≠ 0 := mul_ne_zero (zpow_ne_zero k hq0) h.u_ne_zero
  have hv'0 : q ^ m * v ≠ 0 := mul_ne_zero (zpow_ne_zero m hq0) h.v_ne_zero
  have hu'pos : (0 : ℝ) < ‖q ^ k * u‖ := norm_pos_iff.mpr hu'0
  have hv'pos : (0 : ℝ) < ‖q ^ m * v‖ := norm_pos_iff.mpr hv'0
  have hu'lat : OffLattice q (q ^ k * u) := h.offLattice_u.zpow_mul hq0 k
  have hv'lat : OffLattice q (q ^ m * v) := h.offLattice_v.zpow_mul hq0 m

  have hα0 : q * (q ^ k * u)⁻¹ ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hu'0)
  have hβ0 : q * (q ^ m * v)⁻¹ ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hv'0)
  have hαlat : OffLattice q (q * (q ^ k * u)⁻¹) := (hu'lat.inv hq0).q_mul hq0
  have hβlat : OffLattice q (q * (q ^ m * v)⁻¹) := (hv'lat.inv hq0).q_mul hq0
  have hα1 : ‖q * (q ^ k * u)⁻¹‖ ≤ 1 := by
    rw [norm_mul, norm_inv]
    exact mul_inv_le_one_of_le hu'pos hk1.le
  have hβ1 : ‖q * (q ^ m * v)⁻¹‖ ≤ 1 := by
    rw [norm_mul, norm_inv]
    exact mul_inv_le_one_of_le hv'pos hm1.le

  have hXα : pointX q (q * (q ^ k * u)⁻¹) = pointX q u := by
    rw [pointX_q_mul hq0, pointX_inv hq0 hu'0 hu'lat, pointX_zpow_mul hq0 k]
  have hXβ : pointX q (q * (q ^ m * v)⁻¹) = pointX q v := by
    rw [pointX_q_mul hq0, pointX_inv hq0 hv'0 hv'lat, pointX_zpow_mul hq0 m]
  have hX' : pointX q (q * (q ^ k * u)⁻¹) = pointX q (q * (q ^ m * v)⁻¹) := by
    rw [hXα, hXβ, hX]

  have hwin : ‖q‖ < ‖(q * (q ^ k * u)⁻¹) * (q * (q ^ m * v)⁻¹)‖ := by
    have hkey : ‖q‖ * (‖q ^ k * u‖ * ‖q ^ m * v‖) < ‖q‖ * ‖q‖ :=
      mul_lt_mul_of_pos_left hC hqpos
    have hprod_pos : (0 : ℝ) < ‖q ^ k * u‖ * ‖q ^ m * v‖ := mul_pos hu'pos hv'pos
    calc ‖q‖ < (‖q‖ * ‖q‖) * (‖q ^ k * u‖ * ‖q ^ m * v‖)⁻¹ :=
          lt_mul_inv_of_mul_lt hprod_pos hkey
      _ = (‖q‖ * ‖q ^ k * u‖⁻¹) * (‖q‖ * ‖q ^ m * v‖⁻¹) := by rw [mul_inv]; ring
      _ = ‖(q * (q ^ k * u)⁻¹) * (q * (q ^ m * v)⁻¹)‖ := by
          rw [norm_mul (q * (q ^ k * u)⁻¹) (q * (q ^ m * v)⁻¹), norm_mul q (q ^ k * u)⁻¹,
            norm_mul q (q ^ m * v)⁻¹, norm_inv (q ^ k * u), norm_inv (q ^ m * v)]
  have hαeq : q * (q ^ k * u)⁻¹ = q ^ (1 + -k) * u⁻¹ := by
    rw [mul_inv, ← zpow_neg, zpow_add₀ hq0, zpow_one]; ring
  have hβeq : q * (q ^ m * v)⁻¹ = q ^ (1 + -m) * v⁻¹ := by
    rw [mul_inv, ← zpow_neg, zpow_add₀ hq0, zpow_one]; ring
  rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hα0 hβ0 hαlat hβlat hα1 hβ1 hwin hX' with
    hcase | hcase
  · rw [hαeq, hβeq] at hcase
    exact (h.inv_left.inv_right).contra_div hcase
  · rw [hαeq, hβeq] at hcase
    exact (h.inv_left.inv_right).contra_mul hcase

private lemma contra_of_norm_lt (hq : ‖q‖₊ < 1) (h : AddParams q u v) {k m : ℤ}
    (hk2 : ‖q ^ k * u‖ ≤ 1) (hm1 : ‖q‖ < ‖q ^ m * v‖)
    (hX : pointX q u = pointX q v)
    (hD : ‖q ^ m * v‖ < ‖q ^ k * u‖) : False := by
  have hq0 := h.q_ne_zero
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu'0 : q ^ k * u ≠ 0 := mul_ne_zero (zpow_ne_zero k hq0) h.u_ne_zero
  have hv'0 : q ^ m * v ≠ 0 := mul_ne_zero (zpow_ne_zero m hq0) h.v_ne_zero
  have hv'pos : (0 : ℝ) < ‖q ^ m * v‖ := norm_pos_iff.mpr hv'0
  have hu'lat : OffLattice q (q ^ k * u) := h.offLattice_u.zpow_mul hq0 k
  have hv'lat : OffLattice q (q ^ m * v) := h.offLattice_v.zpow_mul hq0 m
  have hβ0 : q * (q ^ m * v)⁻¹ ≠ 0 := mul_ne_zero hq0 (inv_ne_zero hv'0)
  have hβlat : OffLattice q (q * (q ^ m * v)⁻¹) := (hv'lat.inv hq0).q_mul hq0
  have hβ1 : ‖q * (q ^ m * v)⁻¹‖ ≤ 1 := by
    rw [norm_mul, norm_inv]
    exact mul_inv_le_one_of_le hv'pos hm1.le
  have hXβ : pointX q (q * (q ^ m * v)⁻¹) = pointX q v := by
    rw [pointX_q_mul hq0, pointX_inv hq0 hv'0 hv'lat, pointX_zpow_mul hq0 m]
  have hX' : pointX q (q ^ k * u) = pointX q (q * (q ^ m * v)⁻¹) := by
    rw [pointX_zpow_mul hq0 k, hXβ, hX]
  have hwin : ‖q‖ < ‖(q ^ k * u) * (q * (q ^ m * v)⁻¹)‖ := by
    have hkey : ‖q‖ * ‖q ^ m * v‖ < ‖q ^ k * u‖ * ‖q‖ := by
      calc ‖q‖ * ‖q ^ m * v‖ < ‖q‖ * ‖q ^ k * u‖ := mul_lt_mul_of_pos_left hD hqpos
        _ = ‖q ^ k * u‖ * ‖q‖ := mul_comm _ _
    calc ‖q‖ < (‖q ^ k * u‖ * ‖q‖) * ‖q ^ m * v‖⁻¹ := lt_mul_inv_of_mul_lt hv'pos hkey
      _ = ‖q ^ k * u‖ * (‖q‖ * ‖q ^ m * v‖⁻¹) := by ring
      _ = ‖(q ^ k * u) * (q * (q ^ m * v)⁻¹)‖ := by
          rw [norm_mul (q ^ k * u) (q * (q ^ m * v)⁻¹), norm_mul q (q ^ m * v)⁻¹,
            norm_inv (q ^ m * v)]
  have hβeq : q * (q ^ m * v)⁻¹ = q ^ (1 + -m) * v⁻¹ := by
    rw [mul_inv, ← zpow_neg, zpow_add₀ hq0, zpow_one]; ring
  rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hu'0 hβ0 hu'lat hβlat hk2 hβ1 hwin hX' with
    hcase | hcase
  · rw [hβeq] at hcase
    exact (h.inv_right).contra_div hcase
  · rw [hβeq] at hcase
    exact (h.inv_right).contra_mul hcase

end Windowed

theorem pointX_ne_of_addParams_of_psiTwo
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hex : ∃ w : K, ‖q‖ < ‖w‖ * ‖w‖ ∧ ‖w‖ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hdiff : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v)))
    (h : AddParams q u v)
    (hpsiu : 2 * pointY q u + pointX q u = 0)
    (hpsiv : 2 * pointY q v + pointX q v = 0) :
    pointX q u ≠ pointX q v := by
  intro hX
  have hqR : ‖q‖ < 1 := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0

  obtain ⟨k, hk1, hk2⟩ := exists_zpow_mul_norm_Ioc hq0 hqR h.u_ne_zero
  obtain ⟨m, hm1, hm2⟩ := exists_zpow_mul_norm_Ioc hq0 hqR h.v_ne_zero

  rcases lt_trichotomy (‖q ^ k * u‖ * ‖q ^ m * v‖) ‖q‖ with hC | hAB | hA
  · exact contra_of_mul_lt hq h hk1 hm1 hX hC
  · rcases lt_trichotomy ‖q ^ k * u‖ ‖q ^ m * v‖ with hD | hEq | hD
    · exact contra_of_norm_lt hq h.swap hm2 hk1 hX.symm hD
    ·
      have hu'sq : ‖q ^ k * u‖ * ‖q ^ k * u‖ = ‖q‖ := by
        rw [hEq] at hAB ⊢; exact hAB
      have hv'sq : ‖q ^ m * v‖ * ‖q ^ m * v‖ = ‖q‖ := by
        rw [← hEq]; exact hu'sq
      have huv_eq : ‖q ^ k * u‖ * ‖q ^ m * v‖ = ‖q‖ := hAB

      have hu'0 : q ^ k * u ≠ 0 := mul_ne_zero (zpow_ne_zero k hq0) h.u_ne_zero
      have hv'0 : q ^ m * v ≠ 0 := mul_ne_zero (zpow_ne_zero m hq0) h.v_ne_zero
      have hu'pos : (0 : ℝ) < ‖q ^ k * u‖ := norm_pos_iff.mpr hu'0
      have hv'pos : (0 : ℝ) < ‖q ^ m * v‖ := norm_pos_iff.mpr hv'0
      have hu'lat : OffLattice q (q ^ k * u) := h.offLattice_u.zpow_mul hq0 k
      have hv'lat : OffLattice q (q ^ m * v) := h.offLattice_v.zpow_mul hq0 m
      have hXu' : pointX q (q ^ k * u) = pointX q u := pointX_zpow_mul hq0 k
      have hXv' : pointX q (q ^ m * v) = pointX q v := pointX_zpow_mul hq0 m
      have hX' : pointX q (q ^ k * u) = pointX q (q ^ m * v) := by rw [hXu', hXv', hX]
      have hpsiu' : 2 * pointY q (q ^ k * u) + pointX q (q ^ k * u) = 0 := by
        rw [pointX_zpow_mul hq0 k, pointY_zpow_mul hq0 k]; exact hpsiu
      have hpsiv' : 2 * pointY q (q ^ m * v) + pointX q (q ^ m * v) = 0 := by
        rw [pointX_zpow_mul hq0 m, pointY_zpow_mul hq0 m]; exact hpsiv

      set u' := q ^ k * u with hu'def
      set v' := q ^ m * v with hv'def

      obtain ⟨ω, hω1, hω2⟩ := hex
      have hωpos : (0 : ℝ) < ‖ω‖ := by nlinarith [norm_nonneg ω]
      have hω0 : ω ≠ 0 := norm_pos_iff.mp hωpos
      have hωgt : ‖q‖ < ‖ω‖ := by nlinarith
      have hωlat : OffLattice q ω := offLattice_of_norm_Ioo hq0 hqR hωgt hω2

      have hu'ω_lt : ‖u' * ω‖ < 1 := by
        rw [norm_mul]
        calc ‖u'‖ * ‖ω‖ ≤ 1 * ‖ω‖ := mul_le_mul_of_nonneg_right hk2 (norm_nonneg ω)
          _ = ‖ω‖ := one_mul _
          _ < 1 := hω2
      have hu'ω_gt : ‖q‖ < ‖u' * ω‖ := by
        rw [norm_mul]
        apply lt_of_mul_self_lt_mul_self hqpos.le (by positivity)
        calc ‖q‖ * ‖q‖ < ‖q‖ * (‖ω‖ * ‖ω‖) := mul_lt_mul_of_pos_left hω1 hqpos
          _ = (‖u'‖ * ‖u'‖) * (‖ω‖ * ‖ω‖) := by rw [hu'sq]
          _ = (‖u'‖ * ‖ω‖) * (‖u'‖ * ‖ω‖) := by ring
      have hv'ω_lt : ‖v' * ω‖ < 1 := by
        rw [norm_mul]
        calc ‖v'‖ * ‖ω‖ ≤ 1 * ‖ω‖ := mul_le_mul_of_nonneg_right hm2 (norm_nonneg ω)
          _ = ‖ω‖ := one_mul _
          _ < 1 := hω2
      have hv'ω_gt : ‖q‖ < ‖v' * ω‖ := by
        rw [norm_mul]
        apply lt_of_mul_self_lt_mul_self hqpos.le (by positivity)
        calc ‖q‖ * ‖q‖ < ‖q‖ * (‖ω‖ * ‖ω‖) := mul_lt_mul_of_pos_left hω1 hqpos
          _ = (‖v'‖ * ‖v'‖) * (‖ω‖ * ‖ω‖) := by rw [hv'sq]
          _ = (‖v'‖ * ‖ω‖) * (‖v'‖ * ‖ω‖) := by ring
      have hu'ωinv_lt : ‖u' * ω⁻¹‖ < 1 := by
        rw [norm_mul, norm_inv]
        apply mul_inv_lt_one_of_lt hωpos
        apply lt_of_mul_self_lt_mul_self (norm_nonneg _) (norm_nonneg _)
        rw [hu'sq]; exact hω1
      have hu'ωinv_gt : ‖q‖ < ‖u' * ω⁻¹‖ := by
        rw [norm_mul, norm_inv]
        apply lt_mul_inv_of_mul_lt hωpos
        calc ‖q‖ * ‖ω‖ < ‖q‖ * 1 := mul_lt_mul_of_pos_left hω2 hqpos
          _ = ‖q‖ := mul_one _
          _ < ‖u'‖ := hk1
      have hv'ωinv_lt : ‖v' * ω⁻¹‖ < 1 := by
        rw [norm_mul, norm_inv]
        apply mul_inv_lt_one_of_lt hωpos
        apply lt_of_mul_self_lt_mul_self (norm_nonneg _) (norm_nonneg _)
        rw [hv'sq]; exact hω1
      have hv'ωinv_gt : ‖q‖ < ‖v' * ω⁻¹‖ := by
        rw [norm_mul, norm_inv]
        apply lt_mul_inv_of_mul_lt hωpos
        calc ‖q‖ * ‖ω‖ < ‖q‖ * 1 := mul_lt_mul_of_pos_left hω2 hqpos
          _ = ‖q‖ := mul_one _
          _ < ‖v'‖ := hm1

      have hPu : AddParams q u' ω :=
        { q_ne_zero := hq0
          u_ne_zero := hu'0
          v_ne_zero := hω0
          offLattice_u := hu'lat
          offLattice_v := hωlat
          offLattice_mul := offLattice_of_norm_Ioo hq0 hqR hu'ω_gt hu'ω_lt
          offLattice_div := offLattice_of_norm_Ioo hq0 hqR hu'ωinv_gt hu'ωinv_lt }
      have hPv : AddParams q v' ω :=
        { q_ne_zero := hq0
          u_ne_zero := hv'0
          v_ne_zero := hω0
          offLattice_u := hv'lat
          offLattice_v := hωlat
          offLattice_mul := offLattice_of_norm_Ioo hq0 hqR hv'ω_gt hv'ω_lt
          offLattice_div := offLattice_of_norm_Ioo hq0 hqR hv'ωinv_gt hv'ωinv_lt }

      have hXuω : pointX q u' ≠ pointX q ω := by
        intro hXeq
        rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hu'0 hω0 hu'lat hωlat hk2 hω2.le
            hu'ω_gt hXeq with hcase | hcase
        · have hcontra : ‖u'‖ * ‖u'‖ = ‖ω‖ * ‖ω‖ := by rw [hcase]
          rw [hu'sq] at hcontra
          exact absurd hcontra (ne_of_lt hω1)
        · have hcontra : ‖u' * ω‖ = 1 := by rw [hcase, norm_one]
          exact absurd hcontra (ne_of_lt hu'ω_lt)
      have hXvω : pointX q v' ≠ pointX q ω := by
        intro hXeq
        rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hv'0 hω0 hv'lat hωlat hm2 hω2.le
            hv'ω_gt hXeq with hcase | hcase
        · have hcontra : ‖v'‖ * ‖v'‖ = ‖ω‖ * ‖ω‖ := by rw [hcase]
          rw [hv'sq] at hcontra
          exact absurd hcontra (ne_of_lt hω1)
        · have hcontra : ‖v' * ω‖ = 1 := by rw [hcase, norm_one]
          exact absurd hcontra (ne_of_lt hv'ω_lt)
      have hΔu : (pointX q u' - pointX q ω) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (sub_ne_zero.mpr hXuω)
      have hΔv : (pointX q v' - pointX q ω) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (sub_ne_zero.mpr hXvω)

      have hDu : pointX q (u' * ω) = pointX q (u' * ω⁻¹) := by
        have h0 : (pointX q (u' * ω) - pointX q (u' * ω⁻¹)) *
            (pointX q u' - pointX q ω) ^ 2 = 0 := by
          rw [hdiff u' ω hPu, hpsiu']; ring
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact sub_eq_zero.mp h1
        · exact absurd h1 hΔu
      have hDv : pointX q (v' * ω) = pointX q (v' * ω⁻¹) := by
        have h0 : (pointX q (v' * ω) - pointX q (v' * ω⁻¹)) *
            (pointX q v' - pointX q ω) ^ 2 = 0 := by
          rw [hdiff v' ω hPv, hpsiv']; ring
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact sub_eq_zero.mp h1
        · exact absurd h1 hΔv

      have hSsum : (pointX q (u' * ω) + pointX q (u' * ω⁻¹)) *
          (pointX q u' - pointX q ω) ^ 2 =
          (pointX q (v' * ω) + pointX q (v' * ω⁻¹)) * (pointX q v' - pointX q ω) ^ 2 := by
        rw [hsum u' ω hPu, hsum v' ω hPv, hX']
      have hΔeq : (pointX q u' - pointX q ω) ^ 2 = (pointX q v' - pointX q ω) ^ 2 := by
        rw [hX']
      have hXsum : pointX q (u' * ω) + pointX q (u' * ω⁻¹) =
          pointX q (v' * ω) + pointX q (v' * ω⁻¹) := by
        rw [hΔeq] at hSsum
        exact mul_right_cancel₀ hΔv hSsum

      have hfinal : pointX q (u' * ω⁻¹) = pointX q (v' * ω⁻¹) := by
        rw [hDu, hDv, ← two_mul, ← two_mul] at hXsum
        exact mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0) hXsum

      have hα0 : u' * ω⁻¹ ≠ 0 := mul_ne_zero hu'0 (inv_ne_zero hω0)
      have hβ0 : v' * ω⁻¹ ≠ 0 := mul_ne_zero hv'0 (inv_ne_zero hω0)
      have hαlat : OffLattice q (u' * ω⁻¹) :=
        offLattice_of_norm_Ioo hq0 hqR hu'ωinv_gt hu'ωinv_lt
      have hβlat : OffLattice q (v' * ω⁻¹) :=
        offLattice_of_norm_Ioo hq0 hqR hv'ωinv_gt hv'ωinv_lt
      have hwin : ‖q‖ < ‖(u' * ω⁻¹) * (v' * ω⁻¹)‖ := by
        have hωω_lt : ‖ω‖ * ‖ω‖ < 1 := by nlinarith [norm_nonneg ω]
        have hωω_pos : (0 : ℝ) < ‖ω‖ * ‖ω‖ := mul_pos hωpos hωpos
        have hkey : ‖q‖ * (‖ω‖ * ‖ω‖) < ‖u'‖ * ‖v'‖ := by
          calc ‖q‖ * (‖ω‖ * ‖ω‖) < ‖q‖ * 1 := mul_lt_mul_of_pos_left hωω_lt hqpos
            _ = ‖q‖ := mul_one _
            _ = ‖u'‖ * ‖v'‖ := huv_eq.symm
        calc ‖q‖ < (‖u'‖ * ‖v'‖) * (‖ω‖ * ‖ω‖)⁻¹ := lt_mul_inv_of_mul_lt hωω_pos hkey
          _ = (‖u'‖ * ‖ω‖⁻¹) * (‖v'‖ * ‖ω‖⁻¹) := by rw [mul_inv]; ring
          _ = ‖(u' * ω⁻¹) * (v' * ω⁻¹)‖ := by
              rw [norm_mul (u' * ω⁻¹) (v' * ω⁻¹), norm_mul u' ω⁻¹, norm_mul v' ω⁻¹,
                norm_inv ω]
      rcases eq_or_mul_eq_one_of_pointX_eq hq0 hq hα0 hβ0 hαlat hβlat
          hu'ωinv_lt.le hv'ωinv_lt.le hwin hfinal with hcase | hcase
      ·
        have huv' : u' = v' := mul_right_cancel₀ (inv_ne_zero hω0) hcase
        rw [hu'def, hv'def] at huv'
        exact h.contra_div huv'
      ·
        have hval : u' * v' = ω * ω := by
          have hexp : ((u' * ω⁻¹) * (v' * ω⁻¹)) * (ω * ω) = u' * v' := by
            calc ((u' * ω⁻¹) * (v' * ω⁻¹)) * (ω * ω)
                = (u' * v') * ((ω⁻¹ * ω) * (ω⁻¹ * ω)) := by ring
              _ = (u' * v') * (1 * 1) := by rw [inv_mul_cancel₀ hω0]
              _ = u' * v' := by ring
          calc u' * v' = ((u' * ω⁻¹) * (v' * ω⁻¹)) * (ω * ω) := hexp.symm
            _ = 1 * (ω * ω) := by rw [hcase]
            _ = ω * ω := one_mul _
        have hnorm : ‖q‖ = ‖ω‖ * ‖ω‖ := by
          calc ‖q‖ = ‖u'‖ * ‖v'‖ := huv_eq.symm
            _ = ‖u' * v'‖ := (norm_mul u' v').symm
            _ = ‖ω * ω‖ := by rw [hval]
            _ = ‖ω‖ * ‖ω‖ := norm_mul ω ω
        exact absurd hnorm (ne_of_lt hω1)
    · exact contra_of_norm_lt hq h hk2 hm1 hX hD
  · exact contra_of_window hq h hk2 hm2 hX hA

theorem symAdd_prod_of_sum_diff_forall_of_exists (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hex : ∃ w : K, ‖q‖ < ‖w‖ * ‖w‖ ∧ ‖w‖ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hdiff : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) :
    ∀ u v : K, AddParams q u v →
      pointX q (u * v) * pointX q (u * v⁻¹) * (pointX q u - pointX q v) ^ 2 =
        symProdNum q (pointX q u) (pointX q v) := by
  intro u v h
  by_cases hne : pointX q u = pointX q v
  ·

    exfalso
    have hS1 := hsum u v h
    have hQ1 := two_mul_pointY_add_pointX_sq hq0 hq h.u_ne_zero h.offLattice_u
    have hQ2 := two_mul_pointY_add_pointX_sq hq0 hq h.v_ne_zero h.offLattice_v
    have hzero : symSumNum q (pointX q u) (pointX q u) = 0 := by
      have h2 : (pointX q u - pointX q v) ^ 2 = 0 := by rw [hne]; ring
      calc symSumNum q (pointX q u) (pointX q u)
          = symSumNum q (pointX q u) (pointX q v) := by rw [hne]
        _ = (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 := hS1.symm
        _ = 0 := by rw [h2, mul_zero]
    have hpsiu : 2 * pointY q u + pointX q u = 0 := by
      have hsq : (2 * pointY q u + pointX q u) ^ 2 = 0 := by
        rw [hQ1]
        simp only [symSumNum] at hzero
        linear_combination hzero
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    have hpsiv : 2 * pointY q v + pointX q v = 0 := by
      have hsq : (2 * pointY q v + pointX q v) ^ 2 = 0 := by
        rw [hQ2, ← hne]
        simp only [symSumNum] at hzero
        linear_combination hzero
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    exact pointX_ne_of_addParams_of_psiTwo hq0 hq hex hsum hdiff h hpsiu hpsiv hne
  · exact symAdd_prod_of_sum_of_diff hq0 hq h.u_ne_zero h.offLattice_u h.v_ne_zero
      h.offLattice_v hne (hsum u v h) (hdiff u v h)

theorem symAddHyps_of_sum_diff_of_exists (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hex : ∃ w : K, ‖q‖ < ‖w‖ * ‖w‖ ∧ ‖w‖ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hdiff : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) :
    SymAddHyps q :=
  symAddHyps_of_sum_prod hq0 hq hsum
    (symAdd_prod_of_sum_diff_forall_of_exists hq0 hq hex hsum hdiff)

theorem symAddHyps_of_sum_diff_of_isAlgClosed [IsAlgClosed K] (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1)
    (hsum : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) + pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        symSumNum q (pointX q u) (pointX q v))
    (hdiff : ∀ u v : K, AddParams q u v →
      (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
        -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))) :
    SymAddHyps q := by
  refine symAddHyps_of_sum_diff_of_exists hq0 hq ?_ hsum hdiff

  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq q (n := 4) (by norm_num)
  have hqR : ‖q‖ < 1 := by exact_mod_cast hq
  have hz0 : z ≠ 0 := by
    intro h0
    apply hq0
    rw [← hz, h0]
    norm_num
  have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have h4 : ‖z‖ ^ 4 = ‖q‖ := by rw [← norm_pow, hz]
  have hzlt : ‖z‖ < 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : (1 : ℝ) ≤ ‖z‖ ^ 4 := by
      calc (1 : ℝ) = 1 ^ 4 := by norm_num
        _ ≤ ‖z‖ ^ 4 := by gcongr
    rw [h4] at h1
    linarith
  have hzz_lt : ‖z‖ * ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  have hzz_pos : (0 : ℝ) < ‖z‖ * ‖z‖ := mul_pos hzpos hzpos
  refine ⟨z, ?_, hzlt⟩
  have hq_eq : ‖q‖ = (‖z‖ * ‖z‖) * (‖z‖ * ‖z‖) := by rw [← h4]; ring
  rw [hq_eq]
  calc (‖z‖ * ‖z‖) * (‖z‖ * ‖z‖) < (‖z‖ * ‖z‖) * 1 := mul_lt_mul_of_pos_left hzz_lt hzz_pos
    _ = ‖z‖ * ‖z‖ := mul_one _

end TateCurve


