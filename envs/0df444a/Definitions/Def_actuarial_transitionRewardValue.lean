-- Prove2me | Definitions.Def_actuarial_transitionRewardValue
-- name    : actuarial_transitionRewardValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:01:18.352268+00:00
-- url     : https://prove2.me/theorems/7ffd8520-2829-40b7-bd41-1f16bd6a3f5f
-- title:
--   Discounted one-step state reward and continuation
-- statement:
--   A cashflow r and continuation value next, both at the next year end, have one-step discounted value averaged over arrival state.
--
--   **Mathematical statement**
--
--   $$
--   V(a)=v\sum_bP_{ab}(r_b+V_{\rm next}(b))
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
open MeasureTheory


namespace ActuarialValuation

noncomputable def transitionRewardValue {S : Type*} [Fintype S]
    (P : S → S → ℝ) (v : ℝ)
    (r next : S → ℝ) (a : S) : ℝ :=
  v * ∑ b : S, P a b * (r b + next b)

end ActuarialValuation


