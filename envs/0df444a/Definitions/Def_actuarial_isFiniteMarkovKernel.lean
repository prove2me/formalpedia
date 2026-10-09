-- Prove2me | Definitions.Def_actuarial_isFiniteMarkovKernel
-- name    : actuarial_isFiniteMarkovKernel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:00:29.764857+00:00
-- url     : https://prove2.me/theorems/95b1bbd3-72dc-478a-be45-a71f1aca05bd
-- title:
--   Nonnegative row-stochastic finite-state transition kernel
-- statement:
--   A one-step transition matrix has nonnegative entries and every starting-state row sums to one.
--
--   **Mathematical statement**
--
--   $$
--   P_{ab}\ge0,\qquad \sum_bP_{ab}=1
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
open MeasureTheory

namespace ActuarialValuation

def isFiniteMarkovKernel {S : Type*} [Fintype S]
    (P : S → S → ℝ) : Prop :=
  (∀ a b : S, 0 ≤ P a b) ∧
    (∀ a : S, (∑ b : S, P a b) = 1)

end ActuarialValuation


