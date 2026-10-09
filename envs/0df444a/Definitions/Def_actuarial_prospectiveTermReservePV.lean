-- Prove2me | Definitions.Def_actuarial_prospectiveTermReservePV
-- name    : actuarial_prospectiveTermReservePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T22:38:45.498952+00:00
-- url     : https://prove2.me/theorems/f9868216-0484-4547-8884-949855bc44c0
-- title:
--   Conditional prospective term-policy reserve
-- statement:
--   Conditional expected future loss per policy surviving to duration t, with an explicit positive-survival condition in interpretation theorems.
--
--   **Mathematical statement**
--
--   $$
--   V_t=\frac{\mathbb E_P[L_{n,t}]}{\Pr(K\ge t)}\quad\text{if }\Pr(K\ge t)>0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 7 §§7.3.1-7.3.3, pages 176-195, prospective loss/policy values and recursion, https://doi.org/10.1017/CBO9780511800146.008; Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, §15.5 stochastic reserves and §6.3 recursions, ISBN 9781118782460.

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
import Definitions.Def_actuarial_futureTermLossPV
open MeasureTheory

namespace ActuarialValuation

noncomputable def prospectiveTermReservePV {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (b π : ℝ) : ℝ :=
  (∫ ω, futureTermLossPV K v n t b π ω ∂P) /
    (P (valuationSurvivalEvent K t)).toReal

end ActuarialValuation


