-- Prove2me | Definitions.Def_WhittEfficiency_MMs_WaitLaw
-- name    : WhittEfficiency_MMs_WaitLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:25.277005+00:00
-- url     : https://prove2.me/theorems/90fb6627-c1b2-40d2-98e8-a48782c9e858
-- title:
--   §3.1, pp. 719–720 — stationary FCFS waiting-time law of an M/M/s queue
-- statement:
--   Consider an $M/M/s$ queue in steady state with Poisson arrival rate $\lambda$, $s\geq1$ servers, exponential service times of mean one, unlimited waiting room, and first-come first-served service. Write $p_n$ for the stationary probability of $n$ customers in the system, and let $W$ be an arriving customer's wait before service.
--
--   The law of $W$ is the mixture
--
--   $$
--   \mathcal L(W)=\left(\sum_{n=0}^{s-1}p_n\right)\delta_0+\sum_{j=0}^{\infty}p_{s+j}\,\operatorname{Gamma}(j+1,s),
--   $$
--
--   where $\operatorname{Gamma}(j+1,s)$ has shape $j+1$ and rate $s$. An arrival finding fewer than $s$ customers waits zero; one finding $s+j$ customers waits through $j+1$ service completions.
--
--   This model gives the waiting-time law from which the conditional exponential result is derived.
--
--   **Formalization Note** The definition uses the stationary state probabilities as arrival-state weights, invoking Poisson arrivals see time averages, and the FCFS exponential-service completion law. It is a modelling definition, not a claim that the conditional law is already exponential.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), pp. 719–720, §3 intro and §3.1; https://doi.org/10.1287/mnsc.38.5.708

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Balance

open MeasureTheory ProbabilityTheory

namespace WhittEfficiency.MMs

/-- The stationary FCFS waiting-time law in the M/M/s queue with individual service rate one.
An arrival seeing fewer than `s` customers waits zero; an arrival seeing `s + j` customers
waits for `j + 1` completions at total rate `s`. The arrival-state weights are the stationary
probabilities, using Poisson arrivals see time averages. -/
noncomputable def waitLaw (s : ℕ) (p : ℕ → ℝ) : Measure ℝ :=
  ENNReal.ofReal (∑ n ∈ Finset.range s, p n) • Measure.dirac 0 +
    Measure.sum (fun j : ℕ => ENNReal.ofReal (p (s + j)) •
      gammaMeasure ((j : ℝ) + 1) s)

end WhittEfficiency.MMs


