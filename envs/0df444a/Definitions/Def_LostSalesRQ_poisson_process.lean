-- Prove2me | Definitions.Def_LostSalesRQ_poisson_process
-- name    : LostSalesRQ_poisson_process
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-17T18:22:33.11319+00:00
-- url     : https://prove2.me/theorems/f264b12c-f158-4ded-adf6-72e1a93ad621
-- title:
--   Unit-rate Poisson demand paths, $W_T(\ell)$ and the calibrated penalty $\alpha_\mu(\eta)$
-- statement:
--   A demand path is the sequence $\xi=(\xi_0,\xi_1,\dots)$ of interarrival times of a rate-one Poisson process; under the canonical law the $\xi_i$ are independent exponential random variables with rate one. The $(k+1)$-st arrival occurs at $S_k=\xi_0+\cdots+\xi_k$ and $N(s)=\#\{k:S_k\le s\}$ counts arrivals in $[0,s]$. A path is regular when all $\xi_i>0$ and $S_k\to\infty$.
--
--   For $T\ge0$ and $0\le\ell\le1$ the expected largest excess of the line $(1-\ell)t$ over demand on $[0,T]$ is
--   $$W_T(\ell)=\mathbb E\sup_{0\le t\le T}\{(1-\ell)t-N(t)\},$$
--   and for $\eta\ge1$ the calibrated penalty (eq. (11)) is
--   $$\alpha_\mu(\eta)=\eta\Big[1+\mathbb E\sup_{0\le t\le\mu}\{(1-1/\eta)t-N(t)\}\Big]=\eta\,[1+W_\mu(1/\eta)].$$
--
--   Proposition 2 identifies $\alpha_\mu(\eta)$ with $B_\mu(\eta)+D_\mu(\eta)$, the penalty at which both lower-bound terms coincide.
--
--   **Formalization Note** The expectation is a Bochner integral of a bounded function of the path. Arrival counts use `Set.ncard`, which is finite on regular paths (a full-measure set).
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.3.2, eq. (11) (p. 13); Appendix D (p. A7).

import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Exponential

/-!
# The unit-rate Poisson demand process

A demand path is the sequence of interarrival times of a rate-one Poisson process; under
`interarrivalLaw` they are independent exponential random variables with rate one.
-/

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set

/-- A demand path: the sequence `ξ 0, ξ 1, …` of unit-rate interarrival times. -/
abbrev DemandPath := ℕ → ℝ

/-- The law of the interarrival times: independent exponential distributions with rate one. -/
noncomputable def interarrivalLaw : Measure DemandPath :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

/-- Epoch `ξ 0 + ⋯ + ξ k` of the `(k+1)`-st arrival of the unit-rate process. -/
def arrivalEpoch (ξ : DemandPath) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ξ i

/-- Number `N(s)` of unit-rate arrivals in `[0, s]`. -/
noncomputable def unitCount (ξ : DemandPath) (s : ℝ) : ℕ :=
  {k : ℕ | arrivalEpoch ξ k ≤ s}.ncard

/-- A demand path is regular when every interarrival time is positive and the arrival epochs
diverge. -/
def RegularPath (ξ : DemandPath) : Prop :=
  (∀ k, 0 < ξ k) ∧ Tendsto (arrivalEpoch ξ) atTop atTop

/-- Largest excess `sup_{0 ≤ t ≤ T} {f t - N(t)}` of the line `f t` over the arrival count. -/
noncomputable def maxExcess (T f : ℝ) (ξ : DemandPath) : ℝ :=
  sSup ((fun t : ℝ => f * t - (unitCount ξ t : ℝ)) '' Icc 0 T)

/-- `W_T(ℓ) = E sup_{0 ≤ t ≤ T} {(1 - ℓ) t - N(t)}` (Appendix D). -/
noncomputable def expectedMaxExcess (T ℓ : ℝ) : ℝ :=
  ∫ ξ, maxExcess T (1 - ℓ) ξ ∂interarrivalLaw

/-- Calibrated penalty `α_μ(η) = η [1 + E sup_{0 ≤ t ≤ μ} {(1 - 1/η) t - N(t)}]` (eq. (11)). -/
noncomputable def calibratedPenalty (μ η : ℝ) : ℝ :=
  η * (1 + expectedMaxExcess μ (1 / η))

end LostSalesRQ


