-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes
-- name    : SharedVehicleApprox_Pricing_Supplement_TravelTimes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:29:52.405009+00:00
-- url     : https://prove2.me/theorems/d3485e09-fe49-4e77-9bc0-87209add7d09
-- title:
--   §2.4 — travel times: states, transition rates, stationary laws, objective, availability, and the constants of §4
-- statement:
--   With **travel times** a state is $(x,y)$: $x_i$ units available at node $i$ and $y_{ij}$ units in transit from $i$ to $j$, with $\sum_ix_i+\sum_{i,j}y_{ij}=m$. Transit times are exponential with mean $\tau_{ij}$. The transitions are
--
--   $$(x,y)\to(x-e_i,\,y+e_{ij})\ \text{ at rate }\ \varphi_{ij}q_{ij}(x,y)\ \ (x_i>0),$$
--
--   $$(x,y)\to(x+e_j,\,y-e_{ij})\ \text{ at rate }\ y_{ij}/\tau_{ij}\ \ (y_{ij}>0).$$
--
--   1. A policy has $q_{ij}(x,y)\in[0,1]$, zero when $x_i=0$. A state-independent $q$ quotes $q_{ij}$ whenever $x_i>0$.
--   2. A stationary law is a probability vector on this finite state space that satisfies global balance. The objective is $\sum_{x,y}\pi(x,y)\sum_{i,j}\varphi_{ij}R_{ij}(q_{ij}(x,y))$.
--   3. $A_m=\max_i\mathbb P[X_i>0]$ is the maximum availability. With $M=\sum_iX_i$ the number of available units, the definitions give $\mathbb P[M=M_0]$ and the law of $(X_i)_i$ given $M=M_0$.
--   4. $\varepsilon_m=2\sqrt{\ln m/m}$, and the factor of Theorems 18 and 34 is $(1-\varepsilon_m)\bigl(\frac{\sqrt{m\ln m}}{\sqrt{m\ln m}+n-1}-\frac{3}{\sqrt{m\ln m}}\bigr)$.
--
--   These objects state Lemmas 16 and 17 and Theorem 18.
--
--   **Formalization Note** The exponential travel time is the paper's notational choice; its remark on general laws (p. 11) is not part of the statements. The conditional law is meaningful when $\mathbb P[M=M_0]>0$, which every statement using it assumes. The logarithm is natural, and the constants are used only for $m\ge100$.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, pp. 10–11 (PDF 11–12), §2.4 and Definition 4; pp. 19–21 (PDF 20–22), §4

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- A state `(x, y)` of the system with travel times (§2.4, p. 10): `x i` units available at node
`i` and `y i j` units in transit from `i` to `j`. -/
abbrev TTState (n : ℕ) : Type := (Fin n → ℕ) × (Fin n → Fin n → ℕ)

/-- The finite state space of the `m`-unit system with travel times:
`∑_i x_i + ∑_{i,j} y_ij = m`. -/
def ttStates (n m : ℕ) : Finset (TTState n) :=
  ((Fintype.piFinset fun _ : Fin n => Finset.range (m + 1)) ×ˢ
      (Fintype.piFinset fun _ : Fin n => Fintype.piFinset fun _ : Fin n =>
        Finset.range (m + 1))).filter
    fun s => (∑ i, s.1 i) + (∑ i, ∑ j, s.2 i j) = m

/-- The vector `e_ij` of one unit in the link queue `ij`. -/
def linkUnit {n : ℕ} (i j : Fin n) : Fin n → Fin n → ℕ :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- The transition rates with travel times (§2.4, pp. 10–11, Definition 4), for exponential transit
times of mean `τ_ij`: `(x, y) → (x − e_i, y + e_ij)` at rate `φ_ij q_ij(x, y)` when `x_i > 0`, and
`(x, y) → (x + e_j, y − e_ij)` at rate `y_ij / τ_ij` when `y_ij > 0`. -/
noncomputable def ttRate {n : ℕ} (φ τ : Fin n → Fin n → ℝ)
    (q : TTState n → Fin n → Fin n → ℝ) (s t : TTState n) : ℝ :=
  ∑ i, ∑ j,
    ((if 0 < s.1 i ∧ t = (s.1 - Pi.single i 1, s.2 + linkUnit i j) then φ i j * q s i j else 0) +
      (if 0 < s.2 i j ∧ t = (s.1 + Pi.single j 1, s.2 - linkUnit i j) then
        (s.2 i j : ℝ) / τ i j else 0))

/-- A state-dependent pricing policy with travel times: at every state each quantile lies in
`[0, 1]` and vanishes when no unit is available at the origin. -/
def IsTTPolicy (n m : ℕ) (q : TTState n → Fin n → Fin n → ℝ) : Prop :=
  ∀ s ∈ ttStates n m, ∀ i j, 0 ≤ q s i j ∧ q s i j ≤ 1 ∧ (s.1 i = 0 → q s i j = 0)

/-- A state-independent quantile matrix run in the system with travel times: `q_ij` while a unit is
available at `i`. -/
def toTTPolicy {n : ℕ} (q : Fin n → Fin n → ℝ) : TTState n → Fin n → Fin n → ℝ :=
  fun s => toPolicy q s.1

/-- A stationary law of the `m`-unit system with travel times under the policy `q`. -/
def IsTTStationary (n m : ℕ) (φ τ : Fin n → Fin n → ℝ)
    (q : TTState n → Fin n → Fin n → ℝ) (π : TTState n → ℝ) : Prop :=
  IsStationaryLaw (ttStates n m) (ttRate φ τ q) π

/-- The steady-state objective with travel times: `∑_s π(s) ∑_{i,j} φ_ij R_ij(q_ij(s))`. -/
def ttObj (n m : ℕ) (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (q : TTState n → Fin n → Fin n → ℝ) (π : TTState n → ℝ) : ℝ :=
  ∑ s ∈ ttStates n m, π s * ∑ i, ∑ j, φ i j * rewardCurve I i j (q s i j)

/-- The maximum availability `A_m = max_i P[X_i > 0]` with travel times. -/
def ttMaxAvailability {n : ℕ} [NeZero n] (m : ℕ) (π : TTState n → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun i => ∑ s ∈ (ttStates n m).filter (fun s => 0 < s.1 i), π s

/-- `P[M = M₀]`, the probability that exactly `M₀` units are available (not in transit). -/
def availableProb {n : ℕ} (m : ℕ) (π : TTState n → ℝ) (M₀ : ℕ) : ℝ :=
  ∑ s ∈ (ttStates n m).filter (fun s => ∑ i, s.1 i = M₀), π s

/-- The law of the node queues conditioned on `M = M₀` (p. 19), used when `P[M = M₀] > 0`. -/
noncomputable def condNodeLaw {n : ℕ} (m : ℕ) (π : TTState n → ℝ) (M₀ : ℕ) :
    (Fin n → ℕ) → ℝ :=
  fun x =>
    if x ∈ states n M₀ then
      (∑ s ∈ (ttStates n m).filter (fun s => s.1 = x), π s) / availableProb m π M₀
    else 0

/-- The scaling parameter `ε_m = 2 √(ln m / m)` (natural logarithm). -/
noncomputable def epsilon (m : ℕ) : ℝ :=
  2 * Real.sqrt (Real.log m / m)

/-- The factor of Theorems 18 and 34:
`(1 − ε_m) (√(m ln m) / (√(m ln m) + n − 1) − 3 / √(m ln m))`. -/
noncomputable def delayFactor (n m : ℕ) : ℝ :=
  (1 - epsilon m) *
    (Real.sqrt (m * Real.log m) / (Real.sqrt (m * Real.log m) + n - 1) -
      3 / Real.sqrt (m * Real.log m))

end SharedVehicleApprox.Pricing.Supplement


