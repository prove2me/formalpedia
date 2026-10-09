-- Prove2me | Definitions.Def_actuarial_futureTermLossPV
-- name    : actuarial_futureTermLossPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T22:36:39.003742+00:00
-- url     : https://prove2.me/theorems/31f28909-6dca-427a-9402-23e0cb3fe995
-- title:
--   Future benefit less premium present value
-- statement:
--   Prospective loss consists only of future cashflows, discounted to the valuation duration.
--
--   **Mathematical statement**
--
--   $$
--   L_{n,t}=bB_{n,t}-\pi Y_{n,t}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_futureTermBenefitPV
import Definitions.Def_actuarial_futureTermPremiumPV
open MeasureTheory

namespace ActuarialValuation

noncomputable def futureTermLossPV {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (b π : ℝ) (ω : Ω) : ℝ :=
  b * futureTermBenefitPV K v n t ω -
    π * futureTermPremiumPV K v n t ω

end ActuarialValuation


