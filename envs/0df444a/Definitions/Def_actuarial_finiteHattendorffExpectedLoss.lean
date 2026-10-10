-- Prove2me | Definitions.Def_actuarial_finiteHattendorffExpectedLoss
-- name    : actuarial_finiteHattendorffExpectedLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T15:23:19.680709+00:00
-- url     : https://prove2.me/theorems/1894abf2-89f3-482e-adf7-e07fef0ad328
-- title:
--   Probability-weighted insurer loss at issue
-- statement:
--   Computes the finite-scenario expectation of issue-date loss with the same scenario probability weights used to derive conditional death probabilities.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E_w[L_n]=\sum_\omega w_\omega L_n(\omega)
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLoss
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteHattendorffExpectedLoss {Ω : Type*}
  [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ)
  (v : ℝ) (premium benefit reserve : ℕ → ℝ) : ℝ :=
  ∑ ω : Ω, w ω * finiteHattendorffLoss K n v premium benefit reserve ω

end ActuarialValuation


