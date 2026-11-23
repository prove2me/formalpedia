-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_RedirectionTravelTimes
-- name    : SharedVehicleApprox_Pricing_Supplement_RedirectionTravelTimes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:31:19.946387+00:00
-- url     : https://prove2.me/theorems/daae20f2-32f6-44f5-a537-69676fbe4e35
-- title:
--   App. D.2 — redirection without prices with travel times: chain, objective and Algorithm 9
-- statement:
--   Every customer is served when a unit is available at the origin, rides take time, and arriving units may be redirected. A state is $(x,y,e)$: available units $x_i$, units $y_{ki}$ carrying a customer, and empty redirected units $e_{ij}$, $m$ in total.
--
--   1. A ride $k\to i$ starts at rate $\varphi_{ki}$ while $x_k>0$ and earns the constant $I_{ki}$. It ends at rate $y_{ki}/\tau_{ki}$. The unit is then sent empty to $j$ with probability $r_{kij}(x,y,e)$, at cost $c_{ij}$, and otherwise becomes available at $i$.
--   2. An empty trip $i\to j$ ends at rate $e_{ij}/\tau_{ij}$; its unit becomes available at $j$ and is not redirected again.
--   3. A policy has $r\ge0$ with $\sum_jr_{kij}\le1$. A stationary law satisfies global balance, and the objective is
--   $$\sum_{x,y,e}\pi(x,y,e)\Bigl(\sum_{k,i}\mathbf 1\{x_k>0\}\varphi_{ki}I_{ki}-\sum_{k,i}\frac{y_{ki}}{\tau_{ki}}\sum_jr_{kij}(x,y,e)c_{ij}\Bigr).$$
--   4. Algorithm 9 maximizes the objective of Algorithm 8 over its constraints and the rate limit
--   $$\sum_{i,j}\tau_{ij}(\varphi_{ij}q_i+z_{ij})\le m.$$
--
--   These objects state Theorem 34.
--
--   **Formalization Note** Occupied and empty transit are separate because only units with a customer may be redirected. Algorithm 9 prints the rate limit as $\sum_{i,j}\varphi_{ij}\tau_{ij}q_i+z_{ij}\le m$. This is a misprint, dimensionally inconsistent, for the constraint that §5.4 states.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, pp. 40–41 (PDF 41–42), App. D.2, Algorithm 9; pp. 10–11 (PDF 11–12), §2.4; p. 25 (PDF 26), §5.1; p. 30 (PDF 31), §5.4

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_NoPricing
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- A state `(x, y, e)` with travel times and supply redirection: `x i` available units at `i`,
`y i j` units carrying a customer from `i` to `j`, and `e i j` empty redirected units travelling
from `i` to `j`. The two kinds of transit are separated because empty units are not redirected
again (p. 25). -/
abbrev RTState (n : ℕ) : Type :=
  (Fin n → ℕ) × (Fin n → Fin n → ℕ) × (Fin n → Fin n → ℕ)

/-- The finite state space: the available, occupied and empty units total `m`. -/
def rtStates (n m : ℕ) : Finset (RTState n) :=
  ((Fintype.piFinset fun _ : Fin n => Finset.range (m + 1)) ×ˢ
      ((Fintype.piFinset fun _ : Fin n => Fintype.piFinset fun _ : Fin n =>
          Finset.range (m + 1)) ×ˢ
        (Fintype.piFinset fun _ : Fin n => Fintype.piFinset fun _ : Fin n =>
          Finset.range (m + 1)))).filter
    fun s => (∑ i, s.1 i) + (∑ i, ∑ j, s.2.1 i j) + (∑ i, ∑ j, s.2.2 i j) = m

/-- A state-dependent redirection policy with travel times: `r s k i j` is the probability that a
trip from `k` ending at `i`, in the state `s` just before it ends, is redirected to `j`. -/
def IsRTPolicy (n m : ℕ) (r : RTState n → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ s ∈ rtStates n m, ∀ k i, (∀ j, 0 ≤ r s k i j) ∧ ∑ j, r s k i j ≤ 1

/-- A state-independent redirection matrix run as a policy with travel times. -/
def toRTPolicy {n : ℕ} (r : Fin n → Fin n → ℝ) :
    RTState n → Fin n → Fin n → Fin n → ℝ :=
  fun _ _ i j => r i j

/-- The transition rates without prices, with travel times and redirection. A customer ride
`k → i` starts at rate `φ_ki` whenever `x_k > 0`. It ends at rate `y_ki / τ_ki`; the unit then
stays at `i`, or leaves empty for `j` with probability `r s k i j`. An empty trip `k → i` ends at
rate `e_ki / τ_ki`, and that unit is not redirected again. -/
noncomputable def rtRate {n : ℕ} (φ τ : Fin n → Fin n → ℝ)
    (r : RTState n → Fin n → Fin n → Fin n → ℝ) (s t : RTState n) : ℝ :=
  ∑ k, ∑ i,
    ((if 0 < s.1 k ∧ t = (s.1 - Pi.single k 1, s.2.1 + linkUnit k i, s.2.2) then φ k i else 0) +
      (if 0 < s.2.1 k i then
        (s.2.1 k i : ℝ) / τ k i *
          ((if t = (s.1 + Pi.single i 1, s.2.1 - linkUnit k i, s.2.2) then
              1 - ∑ j, r s k i j else 0) +
            ∑ j, if t = (s.1, s.2.1 - linkUnit k i, s.2.2 + linkUnit i j) then r s k i j else 0)
      else 0) +
      (if 0 < s.2.2 k i ∧ t = (s.1 + Pi.single i 1, s.2.1, s.2.2 - linkUnit k i) then
        (s.2.2 k i : ℝ) / τ k i else 0))

/-- A stationary law of the `m`-unit system under the redirection policy `r`. -/
def IsRTStationary (n m : ℕ) (φ τ : Fin n → Fin n → ℝ)
    (r : RTState n → Fin n → Fin n → Fin n → ℝ) (π : RTState n → ℝ) : Prop :=
  IsStationaryLaw (rtStates n m) (rtRate φ τ r) π

/-- The steady-state objective: `I_ki` for every ride started from `k` to `i`, minus `c_ij` for
every redirection from `i` to `j`. -/
noncomputable def rtObj (n m : ℕ) (φ τ I c : Fin n → Fin n → ℝ)
    (r : RTState n → Fin n → Fin n → Fin n → ℝ) (π : RTState n → ℝ) : ℝ :=
  ∑ s ∈ rtStates n m, π s *
    ((∑ k, ∑ i, if 0 < s.1 k then φ k i * I k i else 0) -
      ∑ k, ∑ i, (s.2.1 k i : ℝ) / τ k i * ∑ j, r s k i j * c i j)

/-- Feasibility in the relaxation of Algorithm 9 (p. 41): the constraints of Algorithm 8 and the
rate limit `∑_{i,j} τ_ij (φ_ij q_i + z_ij) ≤ m` (§5.4, p. 30). Algorithm 9 prints it as
`∑_{i,j} φ_ij τ_ij q_i + z_ij ≤ m`, a misprint. -/
def IsAlg9Feasible {n : ℕ} (φ τ : Fin n → Fin n → ℝ) (m : ℕ) (q : Fin n → ℝ)
    (z : Fin n → Fin n → ℝ) : Prop :=
  IsAlg8Feasible φ q z ∧ ∑ i, ∑ j, τ i j * (φ i j * q i + z i j) ≤ m

/-- `(q, z)` is an optimal solution of the relaxation of Algorithm 9. -/
def IsAlg9Optimal {n : ℕ} (φ τ I c : Fin n → Fin n → ℝ) (m : ℕ) (q : Fin n → ℝ)
    (z : Fin n → Fin n → ℝ) : Prop :=
  IsAlg9Feasible φ τ m q z ∧
    ∀ q' z', IsAlg9Feasible φ τ m q' z' → alg8Obj φ I c q' z' ≤ alg8Obj φ I c q z

end SharedVehicleApprox.Pricing.Supplement


