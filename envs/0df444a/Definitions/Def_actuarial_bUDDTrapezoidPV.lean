-- Prove2me | Definitions.Def_actuarial_bUDDTrapezoidPV
-- name    : actuarial_bUDDTrapezoidPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:45:51.663468+00:00
-- url     : https://prove2.me/theorems/ae593704-22e1-4443-9bfa-d7cd2cc59263
-- title:
--   Integral of linearly interpolated finite UDD survival
-- statement:
--   The trapezoidal survivor sum equals the integral over each calendar year of survival linearly interpolated under UDD.
--
--   Mathematical relation:
--
--   $$
--   C=\sum_{j=0}^{h-1}\frac{S(j)+S(j+1)}2
--   $$
--
--   Units: GBP per unit annual pension, with yearly integration intervals and dimensionless survival probabilities. All displayed results are open Lean theorem statements, not accepted proofs.
-- source:
--   Original derived actuarial result, contextual source page 166. David C. M. Dickson, Mary R. Hardy and Howard R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5, Cambridge University Press. https://doi.org/10.1017/9781108784184 This exact finite UDD payment-event identity, including terminal censoring and instalment scale, is original to this formalisation; it is not a verbatim numbered theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

noncomputable def bUDDTrapezoidPV (h : ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range h, (bSurvival h p j + bSurvival h p (j+1))/2

end ActuarialAnnuities


