-- Prove2me | Definitions.Def_actuarial_f_gmpAdjustedDirectEPV
-- name    : actuarial_f_gmpAdjustedDirectEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:44:52.796149+00:00
-- url     : https://prove2.me/theorems/47477d25-61ed-4da3-b50e-b22ebc07558a
-- title:
--   GMP-adjusted direct joint-state EPV
-- statement:
--   Direct expected present value of the arbitrary-supplement parallel-payment comparator under a finite joint award/mortality law. No statutory eligibility predicate is built into its supplied member or survivor supplement functions.
-- source:
--   Original derived finite-sum actuarial identity, supported context in Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, Chapters 10–11: https://doi.org/10.1017/9781108784184 . Statutory entitlement requires separate inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_gmpAdjustedParallelInstalment

namespace ActuarialUnderpinsF
noncomputable def gmpAdjustedDirectEPV
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (survivorSupplement : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  expect n h p (fun z i j =>
    ∑ t ∈ Finset.range (h + 1), disc t *
      gmpAdjustedParallelInstalment h r g z i j t a b c sa sb
        estate ga gb gc gs ge memberSupplement survivorSupplement)
end ActuarialUnderpinsF


