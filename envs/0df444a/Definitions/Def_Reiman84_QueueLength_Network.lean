-- Prove2me | Definitions.Def_Reiman84_QueueLength_Network
-- name    : Reiman84_QueueLength_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:27:19.564967+00:00
-- url     : https://prove2.me/theorems/63293819-d2e7-42a6-befe-c7aeac88df05
-- title:
--   Section 2 — the open queueing network built from IID interarrival, service and routing sequences, and Harrison's representation (1)–(3)
-- statement:
--   This file sets up the queueing network of §2 of Reiman (1984). There are $K$ single-server stations and a nonempty set $\mathcal J\subseteq\{1,\dots,K\}$ of stations receiving arrivals from outside.
--
--   1. **Primitives.** On a probability space $(\Omega,\mathcal F,P)$ there are mutually independent sequences of IID random variables $\{u_j^i\}_{i\ge1}$ ($j\in\mathcal J$), $\{v_k^i\}_{i\ge1}$, $\{\phi_k^i\}_{i\ge1}$ ($1\le k\le K$). The $u_k^i$ (interarrival times from outside to station $k$) and $v_k^i$ (the $i$th service time at station $k$) are strictly positive and have finite variance; $\phi_k^i\in\{0,1,\dots,K\}$ is the routing indicator of the $i$th customer served at station $k$, the value $0$ meaning that the customer leaves.
--
--   2. **Parameters.** $\mu_k=(E[v_k^1])^{-1}$, $s_k=\operatorname{var}(v_k^1)$, $\lambda_k=(E[u_k^1])^{-1}$ and $a_k=\operatorname{var}(u_k^1)$ for $k\in\mathcal J$, $\lambda_k=0$ for $k\notin\mathcal J$; the routing matrix $P=(p_{kj})$, $p_{kj}=P\{\phi_k^1=j\}$, has spectral radius strictly less than one; $\nu=\lambda+\mu P$.
--
--   3. **Renewal processes.** $U_k(l)=\sum_{i=1}^l u_k^i$, $V_k(l)=\sum_{i=1}^l v_k^i$, $A_k(t)=\max\{l\ge0:U_k(l)\le t\}$ ($A_k\equiv0$ for $k\notin\mathcal J$), $S_k(t)=\max\{l\ge0:V_k(l)\le t\}$, and
--   $$\hat S_k(t)=\sum_{i=1}^{S_k(t)}\Phi_k^i-S_k(t)e_k,\qquad \Phi_k^i=e_{\phi_k^i},$$
--   where $e_j$ is the $j$th unit row vector and $e_0=0$.
--
--   4. **Queue length (Harrison's representation).** $(Q,B)$ solves
--   $$Q(0)\in\mathbb Z_+^K,\quad B_k(0)=0,\quad B_k(t)=\int_0^t 1_{\{Q_k(s)>0\}}\,ds,\quad Q(t)=A(t)+\sum_{k=1}^K\hat S_k(B_k(t))\quad(t\ge0).$$
--   $I_k(t)=t-B_k(t)$ is the cumulative idleness.
--
--   5. **Centred processes** (pp. 444). $X(t)=A(t)+\sum_k\hat S_k(t)$, $\tilde A(t)=A(t)-\lambda t$, $\tilde S_k(t)=\hat S_k(t)-\mu_k(P-I)_k t$ with $(P-I)_k$ the $k$th row of $P-I$, $\eta=\mu(P-I)$,
--   $$\tilde X(t)=\Big[\tilde A(t)+\sum_{k=1}^K\tilde S_k(B_k(t))\Big]+(\lambda+\eta)t,$$
--   and $Y_k(t)=\mu_k I_k(t)$.
--
--   These objects carry every statement about a single network; §3 takes a sequence of them.
--
--   **Formalization Note** Stations are `Fin K` (0-based), the $i$th variable of a sequence ($i\ge1$) has index $i-1$, and a routing indicator is an element of `Fin (K+1)` with `0` for "leaves" and `j.succ` for station `j`. Mutual independence of all primitive variables is `iIndep` of the σ-algebras they generate. Positivity of $u$, $v$ is required at every sample point. The maxima defining $A_k$, $S_k$ are `sSup` of subsets of `ℕ`; they are the true maxima whenever $U_k(l)\to\infty$, $V_k(l)\to\infty$, which holds almost surely. "Spectral radius strictly less than one" is stated as $P^m\to0$, which is equivalent (spectral radius over $\mathbb C$). Equation (2) is stated for paths $s\mapsto Q_k(s)$ that are Lebesgue measurable, so that the integral is meaningful.
-- source:
--   Reiman, Open Queueing Networks in Heavy Traffic, Math. Oper. Res. 9(3) (1984), pp. 442–444, Section 2, Eqs. (1a), (1b), (2), (3), (5)–(10), and Y on p. 444

import Mathlib

namespace Reiman84.QueueLength

open Filter Topology MeasureTheory ProbabilityTheory Matrix

/-!
Reiman (1984), §2 (pp. 442–445): one open queueing network with `K` single-server stations,
built from mutually independent IID interarrival, service and routing sequences; its
parameters; the renewal processes; the queue-length equations (1)–(3); and the processes
`I`, `X`, `X̃`, `Y` of (5)–(13).

Conventions. Stations are `Fin K` (station `k` of the paper is `k : Fin K`, 0-based). The
paper's `i`th variable of a sequence (`i ≥ 1`) is the entry with index `i − 1 : ℕ`. A routing
indicator takes values in `{0, 1, …, K}`; it is encoded in `Fin (K + 1)`, where `0` means
"leaves the network" and `j.succ` means "routed to station `j`". Vectors are row vectors
`Fin K → ℝ`.
-/

/-- The routing vector `Φ = e_φ` of p. 443: for `φ = j.succ` it is the unit row vector `e_j`;
for `φ = 0` (the customer leaves) it is the zero vector. -/
def routeVec {K : ℕ} (r : Fin (K + 1)) : Fin K → ℝ :=
  fun j => if r = j.succ then 1 else 0

/-- Index set of the primitive sequences: interarrival times `u_kⁱ` (`k ∈ 𝒥`), service times
`v_kⁱ` and routing indicators `φ_kⁱ` (`1 ≤ k ≤ K`), `i ≥ 1`. -/
abbrev PrimIndex (K : ℕ) (J : Finset (Fin K)) : Type :=
  ({k // k ∈ J} × ℕ) ⊕ (Fin K × ℕ) ⊕ (Fin K × ℕ)

/-- The routing matrix `P = (p_kj)`, `p_kj = P{φ_k¹ = j}` (p. 442), of routing indicators `φ`. -/
noncomputable def routingMatrixOf {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (φ : Fin K → ℕ → Ω → Fin (K + 1)) : Matrix (Fin K) (Fin K) ℝ :=
  fun k j => P.real {ω | φ k 0 ω = j.succ}

/-- An open queueing network of §2 (pp. 442–443) on the probability space `(Ω, 𝓕, P)`, with
`K` stations and the nonempty set `𝒥 ⊆ {1, …, K}` of stations receiving exogenous arrivals:
* `u k i` is `u_k^{i+1}`, the interarrival time from outside to station `k ∈ 𝒥`;
* `v k i` is `v_k^{i+1}`, the `(i+1)`st service time at station `k`;
* `φ k i` is `φ_k^{i+1}`, the routing indicator of the `(i+1)`st customer served at `k`;
the sequences are mutually independent, each is IID, the `u` and `v` are strictly positive,
`μ_k = (E v_k¹)⁻¹`, `s_k = var v_k¹`, `λ_k = (E u_k¹)⁻¹`, `a_k = var u_k¹` are finite (the
variables are square integrable), and the routing matrix has spectral radius strictly less
than one, stated as `Pᵐ → 0`. -/
structure Network (K : ℕ) (J : Finset (Fin K)) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) where
  /-- Interarrival times: `u k i = u_k^{i+1}` (used for `k ∈ 𝒥` only). -/
  u : Fin K → ℕ → Ω → ℝ
  /-- Service times: `v k i = v_k^{i+1}`. -/
  v : Fin K → ℕ → Ω → ℝ
  /-- Routing indicators: `φ k i = φ_k^{i+1} ∈ {0, 1, …, K}`. -/
  φ : Fin K → ℕ → Ω → Fin (K + 1)
  isProb : IsProbabilityMeasure P
  J_nonempty : J.Nonempty
  meas_u : ∀ k ∈ J, ∀ i, Measurable (u k i)
  meas_v : ∀ k i, Measurable (v k i)
  meas_φ : ∀ k i, Measurable (φ k i)
  /-- The sequences are mutually independent sequences of independent random variables. -/
  indep : iIndep (fun ι : PrimIndex K J => match ι with
      | Sum.inl (k, i) => MeasurableSpace.comap (u k.1 i) inferInstance
      | Sum.inr (Sum.inl (k, i)) => MeasurableSpace.comap (v k i) inferInstance
      | Sum.inr (Sum.inr (k, i)) => MeasurableSpace.comap (φ k i) inferInstance) P
  ident_u : ∀ k ∈ J, ∀ i, IdentDistrib (u k i) (u k 0) P P
  ident_v : ∀ k i, IdentDistrib (v k i) (v k 0) P P
  ident_φ : ∀ k i, IdentDistrib (φ k i) (φ k 0) P P
  pos_u : ∀ k ∈ J, ∀ i ω, 0 < u k i ω
  pos_v : ∀ k i ω, 0 < v k i ω
  memLp_u : ∀ k ∈ J, MemLp (u k 0) 2 P
  memLp_v : ∀ k, MemLp (v k 0) 2 P
  /-- Spectral radius of `P = (p_kj)` strictly less than one, i.e. `Pᵐ → 0`. -/
  spectral : Tendsto (fun m : ℕ => routingMatrixOf P φ ^ m) atTop (𝓝 0)

namespace Network

variable {K : ℕ} {J : Finset (Fin K)} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The routing matrix `P = (p_kj)` of the network. -/
noncomputable def routing (N : Network K J P) : Matrix (Fin K) (Fin K) ℝ :=
  routingMatrixOf P N.φ

/-- `μ_k = (E[v_k¹])⁻¹`, the service rate at station `k`. -/
noncomputable def mu (N : Network K J P) (k : Fin K) : ℝ :=
  (∫ ω, N.v k 0 ω ∂P)⁻¹

/-- `s_k = var(v_k¹)`. -/
noncomputable def sVar (N : Network K J P) (k : Fin K) : ℝ :=
  variance (N.v k 0) P

/-- `λ_k = (E[u_k¹])⁻¹` for `k ∈ 𝒥`, and `λ_k = 0` for `k ∉ 𝒥` (p. 443). -/
noncomputable def lam (N : Network K J P) (k : Fin K) : ℝ :=
  if k ∈ J then (∫ ω, N.u k 0 ω ∂P)⁻¹ else 0

/-- `a_k = var(u_k¹)` (meaningful for `k ∈ 𝒥`). -/
noncomputable def aVar (N : Network K J P) (k : Fin K) : ℝ :=
  variance (N.u k 0) P

/-- `ν = λ + μP` (p. 444), as a row vector. -/
noncomputable def nu (N : Network K J P) : Fin K → ℝ :=
  N.lam + Matrix.vecMul N.mu N.routing

/-- `U_k(l) = ∑_{i=1}^{l} u_kⁱ`, `U_k(0) = 0`. -/
noncomputable def U (N : Network K J P) (k : Fin K) (l : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range l, N.u k i ω

/-- `V_k(l) = ∑_{i=1}^{l} v_kⁱ`, `V_k(0) = 0`. -/
noncomputable def V (N : Network K J P) (k : Fin K) (l : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range l, N.v k i ω

/-- `A_k(t) = max{l ≥ 0 : U_k(l) ≤ t}` for `k ∈ 𝒥`, and `A_k(t) = 0` for `k ∉ 𝒥` (p. 443).
(The maximum exists whenever `U_k(l) → ∞`, which holds almost surely.) -/
noncomputable def A (N : Network K J P) (k : Fin K) (t : ℝ) (ω : Ω) : ℕ :=
  if k ∈ J then sSup {l : ℕ | N.U k l ω ≤ t} else 0

/-- `S_k(t) = max{l ≥ 0 : V_k(l) ≤ t}` (p. 443). -/
noncomputable def S (N : Network K J P) (k : Fin K) (t : ℝ) (ω : Ω) : ℕ :=
  sSup {l : ℕ | N.V k l ω ≤ t}

/-- The vector process `A(t)` with components `A_k(t)`. -/
noncomputable def Avec (N : Network K J P) (t : ℝ) (ω : Ω) : Fin K → ℝ :=
  fun k => (N.A k t ω : ℝ)

/-- `Ŝ_k(t) = ∑_{i=1}^{S_k(t)} Φ_kⁱ − S_k(t) e_k` (p. 443), `Φ_kⁱ = e_{φ_kⁱ}`. -/
noncomputable def Shat (N : Network K J P) (k : Fin K) (t : ℝ) (ω : Ω) : Fin K → ℝ :=
  (∑ i ∈ Finset.range (N.S k t ω), routeVec (N.φ k i ω)) - (N.S k t ω : ℝ) • Pi.single k 1

/-- `(Q, B)` solves (1a), (1b), (2), (3) of p. 443 at the sample point `ω`:
* (1a) `Q(0) ∈ ℤ₊^K`;
* (1b) `B_k(0) = 0`;
* (2) `B_k(t) = ∫_0^t 1{Q_k(s) > 0} ds` for `t ≥ 0` (the paths `s ↦ Q_k(s)` are required to be
  measurable, so that the integral is the Lebesgue integral of the indicator);
* (3) `Q(t) = A(t) + ∑_k Ŝ_k(B_k(t))` for `t ≥ 0`. -/
def IsQueueSolution (N : Network K J P) (ω : Ω) (Q B : ℝ → Fin K → ℝ) : Prop :=
  (∀ k, ∃ m : ℕ, Q 0 k = m) ∧
  (∀ k, B 0 k = 0) ∧
  (∀ k, Measurable (fun s => Q s k)) ∧
  (∀ k, ∀ t, 0 ≤ t → B t k = ∫ s in (0 : ℝ)..t, if 0 < Q s k then (1 : ℝ) else 0) ∧
  (∀ t, 0 ≤ t → Q t = N.Avec t ω + ∑ k, N.Shat k (B t k) ω)

/-- The cumulative idleness `I_k(t) = t − B_k(t)` (p. 443). -/
def idle (B : ℝ → Fin K → ℝ) (t : ℝ) : Fin K → ℝ :=
  fun k => t - B t k

/-- `X(t) = A(t) + ∑_k Ŝ_k(t)`, (5) p. 444. -/
noncomputable def X (N : Network K J P) (t : ℝ) (ω : Ω) : Fin K → ℝ :=
  N.Avec t ω + ∑ k, N.Shat k t ω

/-- `Ã(t) = A(t) − λt`, (6). -/
noncomputable def Atilde (N : Network K J P) (t : ℝ) (ω : Ω) : Fin K → ℝ :=
  N.Avec t ω - t • N.lam

/-- `S̃_k(t) = Ŝ_k(t) − μ_k (P − I)_k t`, (7), `(P − I)_k` the `k`th row of `P − I`. -/
noncomputable def Stilde (N : Network K J P) (k : Fin K) (t : ℝ) (ω : Ω) : Fin K → ℝ :=
  N.Shat k t ω - (N.mu k * t) • (N.routing - 1) k

/-- `η = μ(P − I)`, (8). -/
noncomputable def eta (N : Network K J P) : Fin K → ℝ :=
  Matrix.vecMul N.mu (N.routing - 1)

/-- `X̃(t) = [Ã(t) + ∑_k S̃_k(B_k(t))] + (λ + η)t`, (10) p. 444, for the busy-time process `B`. -/
noncomputable def Xtilde (N : Network K J P) (B : ℝ → Fin K → ℝ) (t : ℝ) (ω : Ω) : Fin K → ℝ :=
  (N.Atilde t ω + ∑ k, N.Stilde k (B t k) ω) + t • (N.lam + N.eta)

/-- `Y_k(t) = μ_k I_k(t)`, p. 444. -/
noncomputable def Y (N : Network K J P) (B : ℝ → Fin K → ℝ) (t : ℝ) : Fin K → ℝ :=
  fun k => N.mu k * idle B t k

end Network

end Reiman84.QueueLength


