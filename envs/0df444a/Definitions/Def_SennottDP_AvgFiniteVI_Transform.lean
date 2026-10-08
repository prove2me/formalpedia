-- Prove2me | Definitions.Def_SennottDP_AvgFiniteVI_Transform
-- name    : SennottDP_AvgFiniteVI_Transform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T09:03:14.448982+00:00
-- url     : https://prove2.me/theorems/73f80e16-2b76-4192-9fc2-adfcdd83dde3
-- title:
--   The aperiodicity transformation Δ* of an MDC (6.64)
-- statement:
--   Fix $0 < \tau < 1$. The **transformed MDC** $\Delta^*$ has the same states and action sets as $\Delta$, costs $C^*(i,a) = \tau C(i,a)$, and transition probabilities
--   $$P^*_{ij}(a) = \tau P_{ij}(a) \quad (j \ne i), \qquad P^*_{ii}(a) = \tau P_{ii}(a) + (1-\tau).$$
--   Each step of $\Delta^*$ is a step of $\Delta$ with probability $\tau$ and a self-loop otherwise. A stationary policy of $\Delta$ is also one of $\Delta^*$.
--
--   The transformation makes every positive recurrent class aperiodic, so value iteration can be applied to $\Delta^*$ when Assumption OPA fails for $\Delta$.
--
--   **Formalization Note** The definition accepts any $\tau \le 1$ (needed for the rows to sum to one); the results assume $0 < \tau < 1$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 120, Eq. (6.64)

import Mathlib
import Definitions.Def_SennottDP_AvgFiniteVI_Model

namespace SennottDP.AvgFiniteVI

open scoped ENNReal NNReal

variable {S : Type*} {Act : Type*} [Countable S]

open Classical in
/-- The aperiodicity transformation `Δ*` of `Δ` (p. 120, (6.64)): for a fixed `0 < τ < 1`, the
same states and action sets, costs `C*(i,a) = τ C(i,a)`, and transition probabilities
`P*_{ij}(a) = τ P_{ij}(a)` for `j ≠ i`, `P*_{ii}(a) = τ P_{ii}(a) + (1 − τ)`. The definition takes
any `τ ≤ 1` (needed for the rows to sum to one); the results assume `0 < τ < 1`. -/
noncomputable def transform (M : MDC S Act) (τ : ℝ≥0) (hτ : τ ≤ 1) : MDC S Act where
  A := M.A
  A_nonempty := M.A_nonempty
  C := fun i a => τ * M.C i a
  P := fun i a j => (τ : ℝ≥0∞) * M.P i a j + if j = i then ((1 - τ : ℝ≥0) : ℝ≥0∞) else 0
  P_sum := by
    intro i a
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, M.P_sum, mul_one, tsum_ite_eq,
      ← ENNReal.coe_add, add_tsub_cancel_of_le hτ, ENNReal.coe_one]

/-- A stationary policy of `Δ` regarded as a stationary policy of `Δ*` (the action sets agree). -/
def StationaryPolicy.toTransform {M : MDC S Act} (e : StationaryPolicy M) (τ : ℝ≥0)
    (hτ : τ ≤ 1) : StationaryPolicy (transform M τ hτ) where
  f := e.f
  mem := e.mem

end SennottDP.AvgFiniteVI


