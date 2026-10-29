-- Prove2me | Definitions.Def_avram_ws01e_bi_new_path_drawdown_proxy
-- name    : avram_ws01e_bi_new_path_drawdown_proxy
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T22:50:59.200708+00:00
-- url     : https://prove2.me/theorems/cb79e615-3232-4bf0-8d67-1ddc9a90399a
-- title:
--   Measurable countable full-path proxy for genuine finite-horizon terminal drawdown
-- statement:
--   For any nonnegative duration and arbitrary nonnegative-time real path, construct a real drawdown proxy by applying minus logarithm to a countable dyadic-ceiling and dense-prefix limsup of exponentiated drawdown. On actual càdlàg Lévy paths, existing accepted lemmas identify it with true terminal drawdown after any time shift. This definition is Pi-product measurable without presuming arbitrary measurable variable-time evaluation.
-- source:
--   Source-faithful reuse of accepted dyadic ceiling prefix rewards 46658681, measurable limsup fac2f5c9, true shifted identity 91c5d4c8 and genuine fresh dyadic limit 5886c047. No independence assumption.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

private noncomputable def avram_ws01e_bi_new_proxy_sample (j : ℕ) : ℝ≥0 :=
  ((Nat.unpair j).2 : ℝ≥0) *
    (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)

private noncomputable def avram_ws01e_bi_new_proxy_ceil
    (t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
    (2 : ℝ≥0) ^ n

private noncomputable def avram_ws01e_bi_new_proxy_reward
    (t : ℝ≥0) (f : ℝ≥0 → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(1 : ℝ) *
    ((⨆ i : ℕ,
      if avram_ws01e_bi_new_proxy_sample i ≤
          avram_ws01e_bi_new_proxy_ceil t n then
        ENNReal.ofReal (f (avram_ws01e_bi_new_proxy_sample i))
      else 0).toReal - f (avram_ws01e_bi_new_proxy_ceil t n))))

noncomputable def AvramDividend.Classical.avram_ws01e_bi_new_path_drawdown_proxy
    (t : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ :=
  Neg.neg (Real.log ((⨅ k : ℕ, ⨆ n : ℕ,
    if k ≤ n then avram_ws01e_bi_new_proxy_reward t f n else 0
      : ℝ≥0∞).toReal))


