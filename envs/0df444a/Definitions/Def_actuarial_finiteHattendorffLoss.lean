-- Prove2me | Definitions.Def_actuarial_finiteHattendorffLoss
-- name    : actuarial_finiteHattendorffLoss
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T15:22:48.553474+00:00
-- url     : https://prove2.me/theorems/838bb5ec-7c0a-4bf9-a042-8952f05dee6c
-- title:
--   Scenario insurer loss including finite terminal reserve
-- statement:
--   Represents the already source-defined finite horizon insurer loss in each probability scenario, preserving the terminal reserve.
--
--   **Mathematical statement**
--
--   $$
--   L_n(\omega)=L_n(K(\omega))
--   $$
-- source:
--   Original derived finite-horizon actuarial declaration. E. S. W. Shiu and X. Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11, printed page 321 (pp. 319–323), Shiu–Xiong (2021), equations (2), (6)–(8), fully discrete Hattendorff variance; https://doi.org/10.1007/s13385-020-00256-9. This individual finite-scenario Lean definition or theorem, including the terminal reserve and finite range, is original derived mathematics rather than a verbatim source theorem. Dependencies: published mortality definitions from Actuarial XVI and published reserve-loss definitions from Actuarial XIX.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteReserveLossAtIssue
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteHattendorffLoss {Ω : Type*}
  (K : Ω → ℕ) (n : ℕ) (v : ℝ)
  (premium benefit reserve : ℕ → ℝ) (ω : Ω) : ℝ :=
  finiteReserveLossAtIssue (K ω) n v premium benefit reserve

end ActuarialValuation


