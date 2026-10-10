-- Prove2me | Definitions.Def_actuarial_finiteHattendorffLossVariance
-- name    : actuarial_finiteHattendorffLossVariance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T15:24:08.591302+00:00
-- url     : https://prove2.me/theorems/5a65473d-dafb-4079-9a20-21045fbc9666
-- title:
--   Probability-weighted insurer loss variance
-- statement:
--   Weighted second central moment of the realised finite-horizon insurer loss under the same finite probability law.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}_w(L_n)=\operatorname{Var}_w(\omega\mapsto L_n(\omega))
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLoss
import Definitions.Def_actuarial_finiteMortalityVariance
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteHattendorffLossVariance {Ω : Type*}
  [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (n : ℕ)
  (v : ℝ) (premium benefit reserve : ℕ → ℝ) : ℝ :=
  finiteMortalityVariance w (finiteHattendorffLoss K n v premium benefit reserve)

end ActuarialValuation


