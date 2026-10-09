-- Prove2me | Definitions.Def_actuarial_twoStepTransition
-- name    : actuarial_twoStepTransition
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:00:44.333889+00:00
-- url     : https://prove2.me/theorems/75cd48b7-f857-4695-9c55-ecb027443d18
-- title:
--   Composition of successive transition matrices
-- statement:
--   The probability of reaching c in two steps from a is a sum over intermediate states b.
--
--   **Mathematical statement**
--
--   $$
--   (PQ)_{ac}=\sum_bP_{ab}Q_{bc}
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def twoStepTransition {S : Type*} [Fintype S]
    (P Q : S → S → ℝ) (a c : S) : ℝ :=
  ∑ b : S, P a b * Q b c

end ActuarialValuation


