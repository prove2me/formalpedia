-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Constants
-- name    : BCFGJPSSV26_Greedy_Constants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:07:24.577385+00:00
-- url     : https://prove2.me/theorems/f756fe15-13af-49e0-8b56-287b768cba5f
-- title:
--   BCFGJPSSV26.Greedy.Constants — The constants of Theorem 1.2
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Constants` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   For each `ε > 0`:
--
--   | regime | `δ` | paper's `ε` | `ε'` |
--   |---|---|---|---|
--   | `ε ≤ 1` | a rational in `(ε/200, ε/100)` | `δ/10` | `25 δ` |
--   | `1 < ε < 4` | `1/100` | `1/1000` | `1/4` |
--   | `ε ≥ 4` | local search | | |
--
--   and one constant `C = 10¹⁰` (`BCFGJPSSV26.Greedy.Cthm`) for all `ε`. The ratio is
--   `(ρ + 10δ)(1 + ε') ≤ 1.9499 + ε` (`BCFGJPSSV26.Greedy.ratio_le`). The trivial solution may have
--   `⌊log₂ n⌋ ⌈1/δ²⌉ ≤ C log n / ε²` extra facilities (`BCFGJPSSV26.Greedy.bcomp_le`); when it has
--   more, `n > ⌊log₂ n⌋ ⌈1/δ²⌉ ≥ 1/δ²`, so `log M = O(log n)` and `6 R ≤ C log n / ε²`
--   (`BCFGJPSSV26.Greedy.sixR_le`). This keeps the bound uniform in `ε`, although after the scaling
--   `log M` is only `O(log n + log(1/ε))` in general.
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.algFor_spec`, `BCFGJPSSV26.Greedy.bcomp_le`, `BCFGJPSSV26.Greedy.sixR_le` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Constants`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Constants.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Constants` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The constants of Theorem 1.2

For each `ε > 0`:

| regime | `δ` | paper's `ε` | `ε'` |
|---|---|---|---|
| `ε ≤ 1` | a rational in `(ε/200, ε/100)` | `δ/10` | `25 δ` |
| `1 < ε < 4` | `1/100` | `1/1000` | `1/4` |
| `ε ≥ 4` | local search | | |

and one constant `C = 10¹⁰` (`BCFGJPSSV26.Greedy.Cthm`) for all `ε`. The ratio is
`(ρ + 10δ)(1 + ε') ≤ 1.9499 + ε` (`BCFGJPSSV26.Greedy.ratio_le`). The trivial solution may have
`⌊log₂ n⌋ ⌈1/δ²⌉ ≤ C log n / ε²` extra facilities (`BCFGJPSSV26.Greedy.bcomp_le`); when it has
more, `n > ⌊log₂ n⌋ ⌈1/δ²⌉ ≥ 1/δ²`, so `log M = O(log n)` and `6 R ≤ C log n / ε²`
(`BCFGJPSSV26.Greedy.sixR_le`). This keeps the bound uniform in `ε`, although after the scaling
`log M` is only `O(log n + log(1/ε))` in general.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- The constant `C` of Theorem 1.2. -/
def Cthm : ℝ := 10 ^ 10

/-- `δ` for `ε ≤ 1`: a rational in `(ε/200, ε/100)`. -/
noncomputable def δsmall (ε : ℝ) : ℚ :=
  if h : 0 < ε then (exists_rat_btwn (by linarith : ε / 200 < ε / 100)).choose else 1 / 100

theorem δsmall_spec {ε : ℝ} (hε : 0 < ε) : ε / 200 < δsmall ε ∧ (δsmall ε : ℝ) < ε / 100 := by
  unfold δsmall
  rw [dif_pos hε]
  exact (exists_rat_btwn (by linarith : ε / 200 < ε / 100)).choose_spec

/-- The constants for `ε < 4`. -/
noncomputable def constsOf (ε : ℝ) : Consts :=
  if ε ≤ 1 then ⟨δsmall ε, δsmall ε / 10, 25 * δsmall ε⟩ else ⟨1 / 100, 1 / 1000, 1 / 4⟩

theorem constsOf_good {ε : ℝ} (hε : 0 < ε) : (constsOf ε).Good := by
  unfold constsOf
  split_ifs with h1
  · obtain ⟨h₁, h₂⟩ := δsmall_spec hε
    have hpos : (0 : ℝ) < δsmall ε := by linarith
    have hle : (δsmall ε : ℝ) ≤ 1 / 100 := by linarith
    have hpos' : (0 : ℚ) < δsmall ε := by exact_mod_cast hpos
    have hle' : δsmall ε ≤ 1 / 100 := by
      have : ((δsmall ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by
        rw [show ((1 / 100 : ℚ) : ℝ) = 1 / 100 by norm_num]
        exact hle
      exact (Rat.cast_le (K := ℝ)).1 this
    exact ⟨hpos', hle', rfl, by positivity, by linarith⟩
  · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The ratio**: `(ρ + 10δ)(1 + ε') ≤ 1.9499 + ε`. -/
theorem ratio_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) :
    ((((ρ + 10 * (constsOf ε).δ) * (1 + (constsOf ε).εp) : ℚ)) : ℝ) ≤ 1.9499 + ε := by
  have hρ : ((ρ : ℚ) : ℝ) = 30466 / 15625 := by
    rw [ρ_eq]
    norm_num
  unfold constsOf
  split_ifs with h1
  · obtain ⟨h₁, h₂⟩ := δsmall_spec hε
    push_cast
    rw [hρ]
    have hδ : (0 : ℝ) < δsmall ε := by linarith
    nlinarith [mul_lt_mul_of_pos_left h₂ hδ]
  · push_cast
    rw [hρ]
    push Not at h1
    norm_num
    linarith

/-- `⌊log₂ n⌋ ≤ 2 log n`, from `log 2 ≥ 1/2`. -/
theorem natLog_two_le_two_log (n : ℕ) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h2 : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have h := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [one_div, Real.log_inv] at this
    linarith
  have := (Nat.cast_nonneg (Nat.log 2 n) : (0 : ℝ) ≤ _)
  nlinarith

/-- `1/δ² ≤ 160000/ε²` for the constants of `ε < 4`. -/
theorem inv_δ_sq_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) :
    1 / ((constsOf ε).δ : ℝ) ^ 2 ≤ 160000 / ε ^ 2 := by
  unfold constsOf
  split_ifs with h1
  · obtain ⟨h₁, -⟩ := δsmall_spec hε
    have hδ : (0 : ℝ) < δsmall ε := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · push Not at h1
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The parameters of `ε < 4`: `ε_g = δ/10` and `ε' = 25 δ`. -/
theorem constsOf_rel {ε : ℝ} (hε : 0 < ε) :
    0 < (constsOf ε).δ ∧ (constsOf ε).δ ≤ 1 / 100 ∧ (constsOf ε).εg = (constsOf ε).δ / 10 ∧
      (constsOf ε).εp = 25 * (constsOf ε).δ := by
  have hc := constsOf_good hε
  refine ⟨hc.δ_pos, hc.δ_le, hc.εg_eq, ?_⟩
  unfold constsOf
  split_ifs <;> norm_num

/-- The number of phases for `ε_g = δ/10` and `ε' = 25 δ`, when `n > ⌊log₂ n⌋ ⌈1/δ²⌉` and
`n ≥ 2`: then `1/δ < n`, `M ≤ n³ + 1`, `⌈log₂ ⌈5 n M⌉⌉ ≤ 12 ⌊log₂ n⌋`, and
`6 R ≤ 7278 ⌊log₂ n⌋ / δ²`. -/
theorem sixR_le_aux {c : Consts} (hδ0 : 0 < c.δ) (hδ1 : c.δ ≤ 1 / 100) (hg : c.εg = c.δ / 10)
    (hp : c.εp = 25 * c.δ) {n : ℕ} (hbn : bcomp c n < n) (hn : 2 ≤ n) :
    ((6 * Rof c n : ℕ) : ℚ) ≤ 7278 * Nat.log 2 n * (1 / c.δ ^ 2) := by
  have hL1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hq1 : 1 ≤ 1 / c.δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `⌈1/δ²⌉ < n`, so `1/δ ≤ 1/δ² < n`
  have hA : ⌈1 / c.δ ^ 2⌉₊ < n := by
    unfold bcomp at hbn
    have : ⌈1 / c.δ ^ 2⌉₊ ≤ Nat.log 2 n * ⌈1 / c.δ ^ 2⌉₊ := Nat.le_mul_of_pos_left _ hL1
    omega
  have hqn : 1 / c.δ ^ 2 < n := by
    have h1 : 1 / c.δ ^ 2 ≤ ⌈1 / c.δ ^ 2⌉₊ := Nat.le_ceil _
    have h2 : (⌈1 / c.δ ^ 2⌉₊ : ℚ) < n := by exact_mod_cast hA
    linarith
  have hinv : 1 / c.δ ≤ 1 / c.δ ^ 2 := by
    rw [div_le_div_iff₀ hδ0 (by positivity)]
    nlinarith
  -- `5 n M ≤ 16 n⁴ ≤ 2^(4 ⌊log₂ n⌋ + 8)`
  have hn0 : (1 : ℚ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hM : 5 * (n : ℚ) * Mof c n ≤ 2 ^ (4 * Nat.log 2 n + 8) := by
    have hn2 : (n : ℚ) ≤ 2 ^ (Nat.log 2 n + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num) n).le
    have hMe : Mof c n = 8 / 25 * (n : ℚ) ^ 2 * (1 / c.δ) + 1 := by
      unfold Mof
      rw [hp]
      field_simp
    rw [hMe]
    have h1 : 1 / c.δ ≤ n := hinv.trans hqn.le
    have h2 : 8 / 25 * (n : ℚ) ^ 2 * (1 / c.δ) ≤ 8 / 25 * (n : ℚ) ^ 2 * n :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (n : ℚ) ^ 4 ≤ (2 ^ (Nat.log 2 n + 1)) ^ 4 := pow_le_pow_left₀ (by positivity) hn2 4
    have h4 : (n : ℚ) ≤ (n : ℚ) ^ 4 := by
      have : (n : ℚ) ^ 1 ≤ (n : ℚ) ^ 4 := pow_le_pow_right₀ hn0 (by norm_num)
      simpa using this
    calc 5 * (n : ℚ) * (8 / 25 * (n : ℚ) ^ 2 * (1 / c.δ) + 1)
        ≤ 5 * (n : ℚ) * (8 / 25 * (n : ℚ) ^ 2 * n + 1) := by gcongr
      _ ≤ 16 * (2 ^ (Nat.log 2 n + 1)) ^ 4 := by nlinarith
      _ = 2 ^ (4 * Nat.log 2 n + 8) := by ring
  have ha : Nat.clog 2 ⌈5 * (n : ℚ) * Mof c n⌉₊ ≤ 12 * Nat.log 2 n := by
    refine (Nat.clog_le_of_le_pow ?_).trans (by omega : 4 * Nat.log 2 n + 8 ≤ 12 * Nat.log 2 n)
    exact Nat.ceil_le.2 (by exact_mod_cast hM)
  -- `⌈1/ε_g²⌉ ≤ 100/δ² + 1`
  have hB : (⌈1 / c.εg ^ 2⌉₊ : ℚ) ≤ 100 * (1 / c.δ ^ 2) + 1 := by
    have h1 : (⌈1 / c.εg ^ 2⌉₊ : ℚ) < 1 / c.εg ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 / c.εg ^ 2 = 100 * (1 / c.δ ^ 2) := by
      rw [hg]
      field_simp
      norm_num
    linarith
  have ha' : (Nat.clog 2 ⌈5 * (n : ℚ) * Mof c n⌉₊ : ℚ) ≤ 12 * Nat.log 2 n := by
    exact_mod_cast ha
  have hL1' : (1 : ℚ) ≤ Nat.log 2 n := by exact_mod_cast hL1
  have hBa := mul_le_mul hB ha' (Nat.cast_nonneg _) (by positivity)
  unfold Rof
  push_cast
  nlinarith

/-! ### The algorithm for `ε` -/

/-- **The algorithm of Theorem 1.2 for `ε`**, on the tuple of an instance. -/
noncomputable def algFor (ε : ℝ) : Raw → List ℕ :=
  if 4 ≤ ε then algLS else algMain (constsOf ε)

theorem log_div_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ Cthm * Real.log n / ε ^ 2 := by
  have := Real.log_natCast_nonneg n
  unfold Cthm
  positivity

end BCFGJPSSV26.Greedy


