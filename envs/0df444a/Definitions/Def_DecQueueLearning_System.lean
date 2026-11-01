-- Prove2me | Definitions.Def_DecQueueLearning_System
-- name    : DecQueueLearning_System
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:39:27.14406+00:00
-- url     : https://prove2.me/theorems/5ac99285-fe75-4635-aeef-0e30600cc886
-- title:
--   Asymmetric bipartite queueing system, flows $\Phi$, rate region $M$, traffic slackness, rate lower bound
-- statement:
--   A **bipartite queueing system** has $N$ queues (agents) $\mathcal N=[N]$ and $K$ servers $\mathcal K=[K]$. Queue $i$ has an arrival rate $\lambda_i\in[0,1]$ and, for each server $j$, a service rate $\mu_{i,j}\in[0,1]$.
--
--   The set of **flows** is
--   $$
--   \Phi=\Big\{\phi\in\mathbb R^{N\times K}:\ \sum_{j'}\phi_{i,j'}\le 1,\ \sum_{i'}\phi_{i',j}\le 1,\ \phi_{i,j}\ge 0\Big\},
--   $$
--   the effective service rate of queue $i$ under $\phi$ is $\mu_i(\phi)=\sum_j\mu_{i,j}\phi_{i,j}$, and $M=\{\mu(\phi):\phi\in\Phi\}$. The set $\Phi$ is also the feasible set $\mathcal S$ of the linear program (Primal).
--
--   1. (**Definition 1**) The system has **traffic slackness** $\varepsilon$ if $(1+\varepsilon)\lambda\in M$.
--   2. A number $\delta$ is a **lower bound on the nonzero service rates** if $\mu_{i,j}\in\{0\}\cup[\delta,1]$ for all $i,j$.
--
--   The module also defines the Lyapunov function $V(Q)=\sum_i Q_i^2$ of a vector of queue lengths. Every theorem of the mission is stated for such a system.
--
--   **Formalization Note** Queues and servers are `Fin N` and `Fin K`; the paper's index $i$ is the Lean index $i+1$.
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, §2, pp. 6–7, Definition 1; V(Q) p. 12

import Mathlib

open Finset

namespace DecQueueLearning

/-- **The asymmetric bipartite queueing system**, Freund–Lykouris–Weng, arXiv:2206.03324v3, §2,
p. 6: `N` queues (agents) and `K` servers, an arrival rate `λᵢ ∈ [0, 1]` for each queue `i` and a
service rate `µᵢⱼ ∈ [0, 1]` for each queue–server pair `(i, j)`.

**Formalization Note** The queues `𝒩 = [N]` and servers `𝒦 = [K]` are `Fin N` and `Fin K`; the
paper's index `i` is the Lean index `i + 1`. -/
structure System (N K : ℕ) where
  /-- The arrival rates `λᵢ`. -/
  lam : Fin N → ℝ
  /-- The service rates `µᵢⱼ`. -/
  mu : Fin N → Fin K → ℝ
  lam_mem : ∀ i, lam i ∈ Set.Icc (0 : ℝ) 1
  mu_mem : ∀ i j, mu i j ∈ Set.Icc (0 : ℝ) 1

/-- The set of flows `Φ = {ϕ : Σⱼ' ϕᵢⱼ' ≤ 1, Σᵢ' ϕᵢ'ⱼ ≤ 1, ϕᵢⱼ ≥ 0}`, arXiv:2206.03324v3, §2, p. 7.
It is also the feasible set `𝒮` of the linear program (Primal) of p. 10. -/
def capacityRegion (N K : ℕ) : Set (Fin N → Fin K → ℝ) :=
  {ϕ | (∀ i, ∑ j, ϕ i j ≤ 1) ∧ (∀ j, ∑ i, ϕ i j ≤ 1) ∧ ∀ i j, 0 ≤ ϕ i j}

/-- The effective service rates `µᵢ(ϕ) = Σⱼ µᵢⱼ ϕᵢⱼ` under a flow `ϕ`, arXiv:2206.03324v3, p. 7. -/
def effectiveRate {N K : ℕ} (s : System N K) (ϕ : Fin N → Fin K → ℝ) : Fin N → ℝ :=
  fun i => ∑ j, s.mu i j * ϕ i j

/-- The set `M = {µ(ϕ) : ϕ ∈ Φ}` of achievable effective service-rate vectors,
arXiv:2206.03324v3, p. 7. -/
def rateRegion {N K : ℕ} (s : System N K) : Set (Fin N → ℝ) :=
  effectiveRate s '' capacityRegion N K

/-- **Definition 1** (traffic slackness), arXiv:2206.03324v3, p. 7: the system has traffic
slackness `ε` if `(1 + ε)λ ∈ M`. -/
def HasTrafficSlackness {N K : ℕ} (s : System N K) (ε : ℝ) : Prop :=
  (fun i => (1 + ε) * s.lam i) ∈ rateRegion s

/-- The lower bound `δ` on the non-zero service rates, arXiv:2206.03324v3, p. 7:
`µᵢⱼ ∈ {0} ∪ [δ, 1]` for all `i, j` (the upper bound `µᵢⱼ ≤ 1` is part of `System`). -/
def HasRateLowerBound {N K : ℕ} (s : System N K) (δ : ℝ) : Prop :=
  ∀ i j, s.mu i j = 0 ∨ δ ≤ s.mu i j

/-- The Lyapunov function `V(Q) = Σᵢ Qᵢ²`, arXiv:2206.03324v3, p. 12. -/
def lyapunov {N : ℕ} (q : Fin N → ℕ) : ℝ := ∑ i, ((q i : ℕ) : ℝ) ^ 2

end DecQueueLearning


