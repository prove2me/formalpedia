-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_DemandRedirection
-- name    : SharedVehicleApprox_Pricing_Supplement_DemandRedirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:27:50.857897+00:00
-- url     : https://prove2.me/theorems/ab7cedea-ad38-4f77-b55d-bcf6da99678e
-- title:
--   §5.1 — demand redirection (matching): policies, move rates, stationary laws, objective and the induced demand
-- statement:
--   A set $E$ of ordered pairs lists, for each node, the nearby nodes whose units can serve its customers. A **policy** quotes $q_{ij}(x)\in[0,1]$ and assigns a willing customer from $i$ to $j$ to a node $k$ with $(i,k)\in E$ with probability $r_{ijk}(x)$, and to $i$ with the remaining probability. A customer assigned to an empty node is lost.
--
--   With $a_{ijk}(x)=r_{ijk}(x)+\mathbf 1\{k=i\}(1-\sum_lr_{ijl}(x))$, the move rate from $x$ to $x-e_k+e_j$ is
--
--   $$w_{kj}(x)=\mathbf 1\{x_k>0\}\sum_i\varphi_{ij}q_{ij}(x)a_{ijk}(x),$$
--
--   a stationary law satisfies the balance equation (1) with these rates, and the objective collects the reward on served rides,
--
--   $$\mathrm{Obj}_m(q,r)=\sum_x\pi(x)\sum_{i,j}\varphi_{ij}R_{ij}(q_{ij}(x))\,s_{ij}(x),\qquad s_{ij}(x)=\sum_{k:x_k>0}a_{ijk}(x).$$
--
--   The **induced demand** of state-independent $(q,r)$ is $\bar\varphi_{kj}=\varphi_{kj}q_{kj}(1-\sum_lr_{kl})+\sum_i\varphi_{ij}q_{ij}r_{ik}$.
--
--   These objects state Theorem 23.
--
--   **Formalization Note** The quantile need not vanish at an empty origin, because a neighbour can serve the customer. The assignment may depend on the destination, which includes every rule that does not.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 27 (PDF 28), §5.1 Demand Redirection

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- A state-dependent pricing and matching policy `(q, r)` on the neighbour graph `E` (§5.1, p. 27).
A willing customer travelling from `i` to `j` is assigned to the neighbour `k`, `(i, k) ∈ E`, with
probability `r x i j k` and to `i` itself with the remaining probability. The quantile need not
vanish when station `i` is empty, since a neighbour can serve the customer. -/
def IsMatchPolicy (n m : ℕ) (E : Finset (Fin n × Fin n))
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ x ∈ states n m, ∀ i j, (0 ≤ q x i j ∧ q x i j ≤ 1) ∧
    (∀ k, 0 ≤ r x i j k) ∧ (∀ k, (i, k) ∉ E → r x i j k = 0) ∧ ∑ k, r x i j k ≤ 1

/-- A state-independent quantile matrix quoted in every state. -/
def toQuote {n : ℕ} (q : Fin n → Fin n → ℝ) : (Fin n → ℕ) → Fin n → Fin n → ℝ :=
  fun _ => q

/-- A state-independent matching matrix run as a policy. -/
def toMatch {n : ℕ} (r : Fin n → Fin n → ℝ) : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ :=
  fun _ i _ k => r i k

/-- The probability that a willing customer from `i` to `j` is assigned to a unit at `k`. -/
def assignProb {n : ℕ} (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) (x : Fin n → ℕ)
    (i j k : Fin n) : ℝ :=
  r x i j k + if k = i then 1 - ∑ l, r x i j l else 0

/-- The probability that a willing customer from `i` to `j` is served: a customer assigned to an
empty node is lost. -/
def serveProb {n : ℕ} (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) (x : Fin n → ℕ)
    (i j : Fin n) : ℝ :=
  ∑ k, if 0 < x k then assignProb r x i j k else 0

/-- The rate, at the state `x`, of the move `x → x − e_k + e_j` under demand redirection. -/
def matchRate {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) : (Fin n → ℕ) → Fin n → Fin n → ℝ :=
  fun x k j => if 0 < x k then ∑ i, φ i j * q x i j * assignProb r x i j k else 0

/-- A stationary law of the `m`-unit system under `(q, r)`: the balance equation (1) with the move
rates `matchRate` in the place of `φ_kj q_kj(x)`. -/
def IsMatchStationary (n m : ℕ) (φ : Fin n → Fin n → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) : Prop :=
  IsStationary n m (fun _ _ => 1) (matchRate φ q r) π

/-- The steady-state objective under demand redirection (p. 27): the per-ride reward at the quoted
quantile, collected on served rides. -/
def matchObj (n m : ℕ) (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) : ℝ :=
  ∑ x ∈ states n m, π x *
    ∑ i, ∑ j, φ i j * rewardCurve I i j (q x i j) * serveProb r x i j

/-- The demand with the same transitions as state-independent `(q, r)`:
`φ̄_kj = φ_kj q_kj (1 − ∑_l r_kl) + ∑_i φ_ij q_ij r_ik`. -/
def matchDemand {n : ℕ} (φ : Fin n → Fin n → ℝ) (q r : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun k j => φ k j * q k j * (1 - ∑ l, r k l) + ∑ i, φ i j * q i j * r i k

end SharedVehicleApprox.Pricing.Supplement


