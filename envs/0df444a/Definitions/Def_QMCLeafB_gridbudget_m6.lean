-- Prove2me | Definitions.Def_QMCLeafB_gridbudget_m6
-- name    : QMCLeafB_gridbudget_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:57:47.467205+00:00
-- url     : https://prove2.me/theorems/52adff73-c539-4201-8be3-4315bbfd5816
-- title:
--   QMCLeafB gridbudget_m6
-- statement:
--   # leaf B phase 16 — the dyadic precision slot of the `RunParts` assembly (member m6, d7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_Core
/-
# leaf B phase 16 — the dyadic precision slot of the `RunParts` assembly (member m6, d7)

`QMCLeafB.RunPartsStream.runParts_shallow_dyadic` (m4's brick 4) leaves the *precision choice*
`grid : ℕ → ℕ` and its scale condition `hgrid1 : ∀ j, 1 ≤ σ_j · 4 ^ (grid j)` as hypotheses, and its
budget `hstatec` charges the bracket widths
`δ_j = γ_j·(invSqrtGe σ_j (grid j) − invSqrtLe σ_j (grid j))` against the recorded margin.

This file closes the *arithmetic* half of that slot.  Nothing about which matrices occur is assumed:
the statements are about a finite family of nonnegative coefficients.

* `invSqrt_width_le_of_scale4` — the honest general accuracy of the reciprocal bracket:
  `invSqrtGe x k − invSqrtLe x k ≤ 4·2^-k/x` as soon as `4 ≤ x·4^k`.  (The shelf's
  `DQ.invSqrt_width_le_of_one_le` covers `x ≥ 1` only; the campaign's cut norms `σ_j` can be far
  below `1` — the dilation only gives `σ ≥ 9m²/(4rmax²)` — so the `4/x` factor is needed.)
* `exists_grid_budget` — for a finite family with a bound `B` on the coefficient mass
  `∑ γ_j·(4/σ_j)·α_j`, a *uniform* grid `g₀ + G` charges at most any prescribed `mh > 0`.

Size: `G = ⌈(B+1)/mh⌉`, so if `B` and `1/mh` have `2^L` size then `G ≤ L + 2` — the grid is a
Poly-sized number, which is what makes it a legal piece of the program's state.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
set_option autoImplicit false

namespace QMCLeafB.GridBudget

noncomputable section

/-! ## 0.  One elementary growth fact (kept local: `Check_budget_bound_m1` cannot be co-loaded with
`Check_DyadicSqrt`, they both carry `DQ`) -/

theorem succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ n ih =>
      have h1 : n + 1 + 1 ≤ 2 * (n + 1) := by omega
      have h2 : 2 * (n + 1) ≤ 2 * 2 ^ n := by omega
      have h3 : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ]; ring
      omega

/-! ## 1.  The general accuracy of the reciprocal bracket -/

/-- **`invSqrtGe − invSqrtLe ≤ 4·2^-k / x` under the scale condition `4 ≤ x·4^k`.** -/
theorem invSqrt_width_le_of_scale4 {x : ℚ} {k : ℕ} (hx : 0 ≤ x) (h : 4 ≤ x * 4 ^ k) :
    DQ.invSqrtGe x k - DQ.invSqrtLe x k ≤ 4 * (1 / 2 ^ k) / x := by
  have hscale : 1 ≤ x * 4 ^ k := by linarith
  have hle : (1 / 2 ^ k : ℚ) ≤ DQ.sqrtLe x k := DQ.inv_two_pow_le_sqrtLe hscale
  have hlt : x < (DQ.sqrtGe x k) ^ 2 := DQ.sq_lt_sqrtGe_sq x k hx
  have hgeo : DQ.sqrtGe x k = DQ.sqrtLe x k + 1 / 2 ^ k := by
    have := DQ.sqrtGe_sub_sqrtLe x k
    linarith
  have hx4 : x < 4 * (DQ.sqrtLe x k) ^ 2 := by
    rw [hgeo] at hlt
    have hposk : (0 : ℚ) < 1 / 2 ^ k := by positivity
    have hs0 : (0 : ℚ) ≤ DQ.sqrtLe x k := DQ.sqrtLe_nonneg x k
    have h0 : (0 : ℚ) ≤ DQ.sqrtLe x k + 1 / 2 ^ k := by linarith
    have h2 : DQ.sqrtLe x k + 1 / 2 ^ k ≤ 2 * DQ.sqrtLe x k := by linarith
    have hsq : (DQ.sqrtLe x k + 1 / 2 ^ k) ^ 2 ≤ (2 * DQ.sqrtLe x k) ^ 2 :=
      pow_le_pow_left₀ h0 h2 2
    nlinarith [hlt, hsq]
  have hpos : 0 < x := by
    have h4 : (0 : ℚ) < 4 ^ k := DQ.four_pow_pos k
    nlinarith [h, h4]
  have hg : DQ.sqrtLe x k ≤ DQ.sqrtGe x k := DQ.sqrtLe_le_sqrtGe x k
  have hP : 0 < DQ.sqrtLe x k * DQ.sqrtGe x k := by
    have h0 : 0 < DQ.sqrtLe x k := DQ.sqrtLe_pos_of_one_le_mul hscale
    have h1 : 0 < DQ.sqrtGe x k := DQ.sqrtGe_pos x k
    positivity
  rw [DQ.invSqrt_width hscale]
  have hk : (0 : ℚ) < 1 / 2 ^ k := by positivity
  have hxq : 0 < x / 4 := by linarith
  have hstep : (1 / 2 ^ k) / (DQ.sqrtLe x k * DQ.sqrtGe x k) ≤ (1 / 2 ^ k) / (x / 4) := by
    rw [div_le_div_iff_of_pos_left hk hP hxq]
    nlinarith [hx4, DQ.sqrtLe_nonneg x k, hg]
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-! ## 2.  A uniform grid makes the charged sum as small as we like -/

/-- **The precision lemma**: a finite charged family can be made to cost at most any `mh > 0` by a
single uniform refinement of the grid, given a bound `B` on its coefficient mass. -/
theorem exists_grid_budget (k : ℕ) (gam sig al : ℕ → ℚ) (g₀ : ℕ) (B mh : ℚ)
    (hgam : ∀ j, 0 ≤ gam j) (hal : ∀ j, 0 ≤ al j) (hsig : ∀ j, 0 < sig j)
    (hscale : ∀ j, 4 ≤ sig j * 4 ^ g₀)
    (hB : ∑ j ∈ Finset.range k, gam j * (4 / sig j) * al j ≤ B) (hB0 : 0 ≤ B)
    (hm : 0 < mh) :
    ∃ G : ℕ, ∑ j ∈ Finset.range k,
        gam j * (DQ.invSqrtGe (sig j) (g₀ + G) - DQ.invSqrtLe (sig j) (g₀ + G)) * al j
      ≤ mh := by
  have hmass0 : (0 : ℚ) ≤ ∑ j ∈ Finset.range k, gam j * (4 / sig j) * al j :=
    Finset.sum_nonneg (fun j _ => by
      have h1 : (0 : ℚ) ≤ 4 / sig j := by
        have := hsig j
        positivity
      exact mul_nonneg (mul_nonneg (hgam j) h1) (hal j))
  obtain ⟨G, hG⟩ : ∃ G : ℕ, (1 : ℚ) / 2 ^ (g₀ + G) ≤ mh / (B + 1) := by
    refine ⟨Nat.ceil ((B + 1) / mh), ?_⟩
    have hpos : (0 : ℚ) < (B + 1) / mh := by positivity
    have hle : (B + 1) / mh ≤ ((Nat.ceil ((B + 1) / mh) : ℕ) : ℚ) := Nat.le_ceil _
    have h2 : ((Nat.ceil ((B + 1) / mh) : ℕ) : ℚ)
        ≤ 2 ^ (g₀ + Nat.ceil ((B + 1) / mh)) := by
      have hG1 : (0 : ℚ) < ((Nat.ceil ((B + 1) / mh) : ℕ) : ℚ) := by linarith
      have hp : ((Nat.ceil ((B + 1) / mh) : ℕ) : ℚ)
          ≤ 2 ^ (Nat.ceil ((B + 1) / mh)) := by
        have := succ_le_two_pow (Nat.ceil ((B + 1) / mh))
        have h3 : ((Nat.ceil ((B + 1) / mh) : ℕ) : ℚ) + 1
            ≤ ((2 ^ Nat.ceil ((B + 1) / mh) : ℕ) : ℚ) := by exact_mod_cast this
        have h3' : ((2 ^ Nat.ceil ((B + 1) / mh) : ℕ) : ℚ)
            = (2 : ℚ) ^ Nat.ceil ((B + 1) / mh) := by push_cast; ring
        linarith [h3, h3']
      have hmono : (2 : ℚ) ^ (Nat.ceil ((B + 1) / mh))
          ≤ 2 ^ (g₀ + Nat.ceil ((B + 1) / mh)) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_add_left _ _)
      linarith
    calc (1 : ℚ) / 2 ^ (g₀ + Nat.ceil ((B + 1) / mh))
        ≤ 1 / ((Nat.ceil ((B + 1) / mh) : ℕ) : ℚ) := by
          apply one_div_le_one_div_of_le _ h2
          linarith
      _ ≤ mh / (B + 1) := by
          have hmne : mh ≠ 0 := ne_of_gt hm
          have hgm : (B + 1) ≤ ((Nat.ceil ((B + 1) / mh) : ℕ) : ℚ) * mh := by
            have hmul := mul_le_mul_of_nonneg_right hle hm.le
            have hcancel : (B + 1) / mh * mh = B + 1 := by
              rw [div_mul_cancel₀ _ hmne]
            linarith [hmul, hcancel]
          have hGpos : (0 : ℚ) < ((Nat.ceil ((B + 1) / mh) : ℕ) : ℚ) := by linarith
          rw [div_le_div_iff₀ hGpos (by linarith : (0 : ℚ) < B + 1)]
          nlinarith [hgm]
  refine ⟨G, ?_⟩
  have hwidth : ∀ j, DQ.invSqrtGe (sig j) (g₀ + G) - DQ.invSqrtLe (sig j) (g₀ + G)
      ≤ 4 * (1 / 2 ^ (g₀ + G)) / sig j := by
    intro j
    apply invSqrt_width_le_of_scale4 (le_of_lt (hsig j))
    have hle : (4 : ℚ) ^ g₀ ≤ 4 ^ (g₀ + G) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
    have hs := hscale j
    have hsp := (hsig j).le
    nlinarith [hle, hs, hsp]
  have hterm : ∀ j ∈ Finset.range k,
      gam j * (DQ.invSqrtGe (sig j) (g₀ + G) - DQ.invSqrtLe (sig j) (g₀ + G)) * al j
        ≤ (1 / 2 ^ (g₀ + G)) * (gam j * (4 / sig j) * al j) := by
    intro j _
    have h1 := hwidth j
    have h3 : (0 : ℚ) ≤ gam j := hgam j
    have h4 : (0 : ℚ) ≤ al j := hal j
    calc gam j * (DQ.invSqrtGe (sig j) (g₀ + G) - DQ.invSqrtLe (sig j) (g₀ + G)) * al j
        ≤ gam j * (4 * (1 / 2 ^ (g₀ + G)) / sig j) * al j := by
          apply mul_le_mul_of_nonneg_right _ h4
          exact mul_le_mul_of_nonneg_left h1 h3
      _ = (1 / 2 ^ (g₀ + G)) * (gam j * (4 / sig j) * al j) := by ring_nf
  have hsum := Finset.sum_le_sum hterm
  have hsplit : ∑ j ∈ Finset.range k, (1 / 2 ^ (g₀ + G)) * (gam j * (4 / sig j) * al j)
      = (1 / 2 ^ (g₀ + G)) * ∑ j ∈ Finset.range k, gam j * (4 / sig j) * al j := by
    rw [Finset.mul_sum]
  rw [hsplit] at hsum
  have hBle : (1 / 2 ^ (g₀ + G)) * ∑ j ∈ Finset.range k, gam j * (4 / sig j) * al j
      ≤ mh / (B + 1) * B := by
    have h1 : (0 : ℚ) ≤ ∑ j ∈ Finset.range k, gam j * (4 / sig j) * al j := hmass0
    calc (1 / 2 ^ (g₀ + G)) * ∑ j ∈ Finset.range k, gam j * (4 / sig j) * al j
        ≤ mh / (B + 1) * ∑ j ∈ Finset.range k, gam j * (4 / sig j) * al j :=
          mul_le_mul_of_nonneg_right hG h1
      _ ≤ mh / (B + 1) * B := by
          apply mul_le_mul_of_nonneg_left hB
          positivity
  have hfinal : (1 / 2 ^ (g₀ + G)) * ∑ j ∈ Finset.range k, gam j * (4 / sig j) * al j ≤ mh := by
    refine le_trans hBle ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0 : ℚ) < B + 1)]
    nlinarith
  linarith

end

/-! ## 3.  Axiom audit -/

#print axioms QMCLeafB.GridBudget.succ_le_two_pow
#print axioms QMCLeafB.GridBudget.invSqrt_width_le_of_scale4
#print axioms QMCLeafB.GridBudget.exists_grid_budget

end QMCLeafB.GridBudget


