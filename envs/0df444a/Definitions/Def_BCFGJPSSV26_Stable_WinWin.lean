-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_WinWin
-- name    : BCFGJPSSV26_Stable_WinWin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:58:49.275775+00:00
-- url     : https://prove2.me/theorems/a651acc0-2fff-4689-9dd4-2b466a771362
-- title:
--   BCFGJPSSV26.Stable.WinWin — The win-win inequalities
-- statement:
--   This is module `BCFGJPSSV26.Stable.WinWin` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Lemma 3.9 and Table 1]: for each
--   optimal cluster, in units of `cost_OPT(C*)`, with `x = per/avg_OPT ≤ 1 + 2ε` and
--   `κ = BCFGJPSSV26.Stable.kappa x`, the `(a, 1 - a)` combination, `a = 3/25`, of the local-search
--   row and the submodular row is at most `1 + η + O(ε)`:
--
--   | clusters | local search | submodular |
--   | --- | --- | --- |
--   | `O_S` | `1 + η` | `1 + η` |
--   | `O_Λᵉ` | `3` | `1 + 2x/e` |
--   | `O_Λˡ ∪ O_P` | `1 + x` | `1 + 2(1 + κ)x/e` |
--   | `O_R` | `2 + x - y_κ` | `1 + x` |
--
--   where for `O_R`, `x ≥ η/(1 + ε)` and `y_κ ≥ 2((1 + κ)x - 1)/κ - εx(1 + 2/κ)`
--   (`BCFGJPSSV26.Stable.row_early`, `BCFGJPSSV26.Stable.row_late`, `BCFGJPSSV26.Stable.row_R`).
--   The main term of the last row has slack only about `6.7 · 10⁻⁴`: at `t = 89/(77 + 65κ)` it reduces
--   to `(1/2 + 1/2000) κ + 2a²/κ ≥ 2a - 1/2000`, by AM–GM.
--
--   **Contents.** The module is published as a whole: 6 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_WinWin`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/WinWin.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Kappa
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.WinWin` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The win-win inequalities

[BCFGJPSSV26b, Lemma 3.9 and Table 1]: for each
optimal cluster, in units of `cost_OPT(C*)`, with `x = per/avg_OPT ≤ 1 + 2ε` and
`κ = BCFGJPSSV26.Stable.kappa x`, the `(a, 1 - a)` combination, `a = 3/25`, of the local-search
row and the submodular row is at most `1 + η + O(ε)`:

| clusters | local search | submodular |
| --- | --- | --- |
| `O_S` | `1 + η` | `1 + η` |
| `O_Λᵉ` | `3` | `1 + 2x/e` |
| `O_Λˡ ∪ O_P` | `1 + x` | `1 + 2(1 + κ)x/e` |
| `O_R` | `2 + x - y_κ` | `1 + x` |

where for `O_R`, `x ≥ η/(1 + ε)` and `y_κ ≥ 2((1 + κ)x - 1)/κ - εx(1 + 2/κ)`
(`BCFGJPSSV26.Stable.row_early`, `BCFGJPSSV26.Stable.row_late`, `BCFGJPSSV26.Stable.row_R`).
The main term of the last row has slack only about `6.7 · 10⁻⁴`: at `t = 89/(77 + 65κ)` it reduces
to `(1/2 + 1/2000) κ + 2a²/κ ≥ 2a - 1/2000`, by AM–GM.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

/-- `e > 2.718`. -/
private theorem exp_one_gt' : (2718 : ℝ) / 1000 < Real.exp 1 :=
  lt_trans (by norm_num) Real.exp_one_gt_d9

/-- The three values of `t`. -/
private theorem tClamp_cases (x : ℝ) :
    (x ≤ 89 / 100 ∧ tClamp x = 89 / 100) ∨ (89 / 100 ≤ x ∧ x ≤ 1 ∧ tClamp x = x) ∨
      (1 ≤ x ∧ tClamp x = 1) := by
  unfold tClamp eta
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]
    rcases le_total (89 / 100) x with h' | h'
    · exact .inr (.inl ⟨h', h, max_eq_right h'⟩)
    · exact .inl ⟨h', max_eq_left h'⟩
  · rw [min_eq_left h, max_eq_right (by norm_num)]
    exact .inr (.inr ⟨h, rfl⟩)

private theorem kappa_mul (x : ℝ) : kappa x * (65 * tClamp x) = 89 - 77 * tClamp x := by
  have h1 := (tClamp_mem x).1
  unfold eta at h1
  have ht : 0 < tClamp x := by linarith
  unfold kappa
  field_simp
  ring

/-- The row of `O_Λᵉ`. -/
theorem row_early {ε x : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1 / 200) (hx : 0 ≤ x) (hx' : x ≤ 1 + 2 * ε) :
    aW * 3 + (1 - aW) * (1 + 2 * x / Real.exp 1) ≤ 1 + eta + 2 * ε := by
  have _ := hε'
  have hE := exp_one_gt'
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  set y := 2 * x / Real.exp 1 with hy
  have hyE : y * Real.exp 1 = 2 * x := by rw [hy]; field_simp
  have hy0 : 0 ≤ y := by positivity
  have h1 : y * (2718 / 1000) ≤ y * Real.exp 1 := mul_le_mul_of_nonneg_left hE.le hy0
  unfold aW eta
  linarith

/-- The row of `O_Λˡ ∪ O_P`. -/
theorem row_late {ε x : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1 / 200) (hx : 0 ≤ x) (hx' : x ≤ 1 + 2 * ε) :
    aW * (1 + x) + (1 - aW) * (1 + 2 * (1 + kappa x) * x / Real.exp 1) ≤ 1 + eta + 3 * ε := by
  have _ := hε'
  have hE := exp_one_gt'
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hk0 := kappa_pos x
  set y := 2 * (1 + kappa x) * x / Real.exp 1 with hy
  have hyE : y * Real.exp 1 = 2 * (1 + kappa x) * x := by rw [hy]; field_simp
  have hy0 : 0 ≤ y := by positivity
  have h1 : y * (2718 / 1000) ≤ y * Real.exp 1 := mul_le_mul_of_nonneg_left hE.le hy0
  have hk := kappa_mul x
  unfold aW eta
  rcases tClamp_cases x with ⟨hx1, ht⟩ | ⟨hx1, hx2, ht⟩ | ⟨hx1, ht⟩
  · rw [ht] at hk
    have hκ : kappa x = 23 / 65 := by linarith
    rw [hκ] at hyE
    linarith
  · rw [ht] at hk
    have hκx : kappa x * x = (89 - 77 * x) / 65 := by linarith
    have : y * Real.exp 1 = 2 * x + 2 * (kappa x * x) := by rw [hyE]; ring
    linarith
  · rw [ht] at hk
    have hκ : kappa x = 12 / 65 := by linarith
    rw [hκ] at hyE
    linarith

/-- The row of `O_R`. -/
theorem row_R {ε x y : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1 / 200) (hx : eta / (1 + ε) ≤ x)
    (hx' : x ≤ 1 + 2 * ε)
    (hy : 2 * ((1 + kappa x) * x - 1) / kappa x - ε * x * (1 + 2 / kappa x) ≤ y) :
    aW * (2 + x - y) + (1 - aW) * (1 + x) ≤ 1 + eta + 10 * ε := by
  set κ := kappa x with hκdef
  have hk0 : 0 < κ := kappa_pos x
  have hkm := kappa_mem x
  rw [← hκdef] at hkm
  have hxpos : 0 < x := by
    refine lt_of_lt_of_le ?_ hx
    unfold eta
    positivity
  have hy' : 2 * ((1 + κ) * x - 1) - ε * x * (κ + 2) ≤ κ * y := by
    have h := mul_le_mul_of_nonneg_left hy hk0.le
    have e : κ * (2 * ((1 + κ) * x - 1) / κ - ε * x * (1 + 2 / κ)) =
        2 * ((1 + κ) * x - 1) - ε * x * (κ + 2) := by
      field_simp
    linarith
  -- the error term
  have herr : 3 / 25 * ε * x * (κ + 2) ≤ 10 * ε * κ := by
    have h1 : x * (κ + 2) ≤ (1 + 2 * ε) * (κ + 2) := mul_le_mul_of_nonneg_right hx' (by linarith)
    have h2 : (1 + 2 * ε) * (κ + 2) ≤ 3 := by nlinarith
    have h3 : 3 / 25 * x * (κ + 2) ≤ 10 * κ := by nlinarith
    have := mul_le_mul_of_nonneg_left h3 hε
    linarith
  -- the main term
  have hk := kappa_mul x
  rw [← hκdef] at hk
  have hmain : κ * x - 6 / 25 * ((1 + κ) * x - 1) ≤ 77 / 100 * κ := by
    rcases tClamp_cases x with ⟨hx1, ht⟩ | ⟨hx1, hx2, ht⟩ | ⟨hx1, ht⟩
    · rw [ht] at hk
      have hκ : κ = 23 / 65 := by linarith
      rw [hκ]
      linarith
    · rw [ht] at hk
      have hpoly : 0 < 7412 / 100 * x ^ 2 - 14253 / 100 * x + 6853 / 100 := by
        nlinarith [sq_nonneg (x - 14253 / 14824)]
      have e : x * (77 / 100 * κ - (κ * x - 6 / 25 * ((1 + κ) * x - 1))) =
          (7412 / 100 * x ^ 2 - 14253 / 100 * x + 6853 / 100) / 65 := by
        linear_combination ((77 / 100 - 19 / 25 * x) / 65) * hk
      have : 0 < x * (77 / 100 * κ - (κ * x - 6 / 25 * ((1 + κ) * x - 1))) := by
        rw [e]
        positivity
      have := (pos_iff_pos_of_mul_pos this).1 hxpos
      linarith
    · rw [ht] at hk
      have hκ : κ = 12 / 65 := by linarith
      rw [hκ]
      linarith
  have hfin : κ * (x - 3 / 25 * y) ≤ κ * (77 / 100 + 10 * ε) := by nlinarith
  have := le_of_mul_le_mul_left hfin hk0
  unfold aW eta
  linarith

end BCFGJPSSV26.Stable


