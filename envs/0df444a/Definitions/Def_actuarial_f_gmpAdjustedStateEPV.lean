-- Prove2me | Definitions.Def_actuarial_f_gmpAdjustedStateEPV
-- name    : actuarial_f_gmpAdjustedStateEPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T12:45:14.974488+00:00
-- url     : https://prove2.me/theorems/53dc1575-436c-441e-a972-77cbc6df71d9
-- title:
--   GMP-adjusted state EPV
-- statement:
--   An independently grouped finite-state valuation of the same supplied member and survivor supplementary streams. The equality to the direct comparator concerns algebraic aggregation and assumes no legal right to offset any statutory survivor component.
-- source:
--   Original derived finite-sum valuation identity, supported context in Dickson, Hardy and Waters (2020), Chapters 10–11: https://doi.org/10.1017/9781108784184 .

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect
import Definitions.Def_actuarial_f_monthlyLinkedStateEPV

namespace ActuarialUnderpinsF
noncomputable def gmpAdjustedStateEPV
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c : ℕ → ℝ) (sa sb : ℕ → ℕ → ℝ)
    (estate ga gb gc : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ)
    (memberSupplement : ℕ → ℕ → ℕ → ℝ)
    (survivorSupplement : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  monthlyLinkedStateEPV n h r g p disc a b c sa sb estate
    ga gb gc gs ge +
  ∑ t ∈ Finset.range (h + 1), disc t *
    expect n h p (fun z i j =>
      memberSupplement z i t + survivorSupplement z i j t)
end ActuarialUnderpinsF


