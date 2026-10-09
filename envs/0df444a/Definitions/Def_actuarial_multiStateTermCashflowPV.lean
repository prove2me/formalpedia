-- Prove2me | Definitions.Def_actuarial_multiStateTermCashflowPV
-- name    : actuarial_multiStateTermCashflowPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T23:11:03.66979+00:00
-- url     : https://prove2.me/theorems/a6a6daf7-2c49-4160-b41d-2a1bc42e275f
-- title:
--   Finite-term multistate benefit and annuity present value
-- statement:
--   Finite aggregate expected PV of state-occupation benefits at the start and transition benefits at the end of each year.
--
--   **Mathematical statement**
--
--   $$
--   V_n=\sum_{k<n}\left[v^k\sum_i\mu_{k,i}c_{k,i}+v^{k+1}\sum_{i,j}\mu_{k,i}P_{k,ij}b_{k,ij}\right]
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_occupationStageReward
import Definitions.Def_actuarial_transitionStageReward
open MeasureTheory

namespace ActuarialValuation

noncomputable def multiStateTermCashflowPV {S : Type*} [Fintype S]
  (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ)
  (v : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    (v ^ k * occupationStageReward (μ k) (c k) +
     v ^ (k + 1) * transitionStageReward (μ k) (P k) (b k))

end ActuarialValuation


