-- Prove2me | Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
-- name    : SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:26:07.415351+00:00
-- url     : https://prove2.me/theorems/ca4c4cd7-53e7-43e0-a392-771ab76fac08
-- title:
--   §5.1 — supply redirection: policies, move rates, stationary laws, objective and the induced demand
-- statement:
--   The system has $n$ nodes, $m$ units, arrival rates $\varphi_{ki}$ and instantaneous rides. Under **supply redirection**, the unit of a ride that ends at $i$ may be sent empty to a node $j$ at cost $c_{ij}$; empty units are not redirected again.
--
--   1. A **policy** is a quantile policy $q_{ki}(x)\in[0,1]$, zero when $x_k=0$, with probabilities $r_{kij}(x)\ge0$, $\sum_jr_{kij}(x)\le1$: a ride $k\to i$ started in state $x$ is redirected to $j$ with probability $r_{kij}(x)$ and stays at $i$ otherwise.
--   2. The **move rate** from $x$ to $x-e_k+e_j$ is
--   $$w_{kj}(x)=\varphi_{kj}q_{kj}(x)\Bigl(1-\sum_lr_{kjl}(x)\Bigr)+\sum_i\varphi_{ki}q_{ki}(x)\,r_{kij}(x).$$
--   A stationary law is a probability vector on $S_{n,m}$ that satisfies the balance equation (1) with these rates.
--   3. With reward curves $R_{ki}$, the **objective** is
--   $$\mathrm{Obj}_m(q,r)=\sum_x\pi(x)\sum_{k,i}\varphi_{ki}\Bigl[R_{ki}(q_{ki}(x))-q_{ki}(x)\sum_jr_{kij}(x)c_{ij}\Bigr].$$
--   4. A state-independent matrix $r$ uses $r_{ij}$ for every trip ending at $i$. The **induced demand** of state-independent $(q,r)$ is $\bar\varphi_{ij}=\varphi_{ij}q_{ij}(1-\sum_kr_{jk})+\sum_k\varphi_{ik}q_{ik}r_{kj}$, the demand of the hypothetical network in the proof of Lemma 21.
--
--   These objects state Lemma 21, Theorem 22, Lemma 30 and Theorem 31.
--
--   **Formalization Note** The redirection probability may depend on the trip's origin as well as on the state before the trip. This includes every rule $r_{ij}(x)$ and every rule that reads the state at arrival. A redirection with $j=i$ is allowed and charged $c_{ii}$, as in Algorithm 3. The balance equation is the base predicate with unit demand and $w$ in the place of the quantiles.
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, pp. 24–26 (PDF 25–27), §5.1 Supply Redirection and the proof of Lemma 21

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

namespace SharedVehicleApprox.Pricing.Supplement

open Finset QueueingFundamentals.Networks

/-- A state-dependent pricing and supply-redirection policy `(q, r)` (§5.1, pp. 24–25): `q` is a
pricing policy, and `r x k i j` is the probability that the unit of a trip from `k` to `i`, started
in the state `x`, is redirected on arrival from `i` to `j`. With probability `1 − ∑ j, r x k i j`
it stays at `i`. -/
def IsRedirectPolicy (n m : ℕ) (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) : Prop :=
  IsPolicy n m q ∧
    ∀ x ∈ states n m, ∀ k i, (∀ j, 0 ≤ r x k i j) ∧ ∑ j, r x k i j ≤ 1

/-- A state-independent redirection matrix run as a policy: every unit arriving at `i` with a
customer is redirected to `j` with probability `r i j`. -/
def toRedirect {n : ℕ} (r : Fin n → Fin n → ℝ) :
    (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ :=
  fun _ _ i j => r i j

/-- The rate, at the state `x`, of the move `x → x − e_k + e_j` under supply redirection: trips
`k → j` that are not redirected, plus trips `k → i` redirected from `i` to `j`. Redirected units
are not redirected again. -/
def redirectRate {n : ℕ} (φ : Fin n → Fin n → ℝ) (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) : (Fin n → ℕ) → Fin n → Fin n → ℝ :=
  fun x k j => φ k j * q x k j * (1 - ∑ l, r x k j l) + ∑ i, φ k i * q x k i * r x k i j

/-- A stationary law of the `m`-unit system under `(q, r)`: the balance equation (1) with the move
rates `redirectRate` in the place of `φ_kj q_kj(x)`. -/
def IsRedirectStationary (n m : ℕ) (φ : Fin n → Fin n → ℝ)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ) : Prop :=
  IsStationary n m (fun _ _ => 1) (redirectRate φ q r) π

/-- The steady-state objective under supply redirection (p. 25): rewards of the rides minus the
cost `c i j` of each redirection from `i` to `j`. -/
def redirectObj (n m : ℕ) (φ : Fin n → Fin n → ℝ) (I : Fin n → Fin n → ℝ → ℝ)
    (c : Fin n → Fin n → ℝ) (q : (Fin n → ℕ) → Fin n → Fin n → ℝ)
    (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ) : ℝ :=
  ∑ x ∈ states n m, π x *
    ∑ k, ∑ i, φ k i * (rewardCurve I k i (q x k i) - q x k i * ∑ j, r x k i j * c i j)

/-- The demand `φ̄` of the hypothetical network in the proof of Lemma 21 (p. 26), which has the
same transitions as state-independent `(q, r)`:
`φ̄_ij = φ_ij q_ij (1 − ∑_k r_jk) + ∑_k φ_ik q_ik r_kj`. -/
def inducedDemand {n : ℕ} (φ : Fin n → Fin n → ℝ) (q r : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => φ i j * q i j * (1 - ∑ k, r j k) + ∑ k, φ i k * q i k * r k j

end SharedVehicleApprox.Pricing.Supplement


