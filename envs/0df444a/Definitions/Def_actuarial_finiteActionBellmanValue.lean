-- Prove2me | Definitions.Def_actuarial_finiteActionBellmanValue
-- name    : actuarial_finiteActionBellmanValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T06:08:25.775087+00:00
-- url     : https://prove2.me/theorems/6327b1e6-7e2f-4e50-974d-0982ed9fad04
-- title:
--   Finite-action discounted Bellman valuation operator
-- statement:
--   Optimises across a nonempty finite collection of admissible actions, each with immediate reward and discounted next-state continuation.
--
--   **Mathematical statement**
--
--   $$
--   (TV)(s)=\max_{a\in A}\left[r(s,a)+v\sum_tP(s,a,t)V(t)\right]
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteActionBellmanValue
  {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : A => reward s a +
      v * (∑ t : S, P s a t * next t))

end ActuarialValuation


