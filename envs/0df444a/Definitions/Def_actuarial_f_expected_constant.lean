-- Prove2me | Definitions.Def_actuarial_f_expected_constant
-- name    : actuarial_f_expected_constant
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T20:02:56.247+00:00
-- url     : https://prove2.me/theorems/a97da3b5-bed9-4ca5-a0d5-bb66758c6741
-- title:
--   Expected constant
-- statement:
--   A normalised joint award and mortality law assigns expected value one to a constant unit cashflow.
--
--   The defining or asserted relationship is:
--
--   $$
--   \mathbb E_p[1]=1
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem actuarial_f_expected_constant (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (hv : 0 < n ∧
      (∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h + 1),
        ∀ j ∈ Finset.range (h + 1), 0 ≤ p z i j) ∧
      (∑ z ∈ Finset.range n, ∑ i ∈ Finset.range (h + 1),
        ∑ j ∈ Finset.range (h + 1), p z i j) = 1) :
    expect n h p (fun z i j => (1 : ℝ)) = 1 := by
  simpa [ActuarialUnderpinsF.expect, ActuarialJointD.expect] using hv.2.2


