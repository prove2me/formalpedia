-- Prove2me | Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
-- name    : QueueingFundamentals_Networks_ClosedJackson
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T08:56:05.513959+00:00
-- url     : https://prove2.me/theorems/ade21284-b7d2-4277-a07a-6b6790371cc1
-- title:
--   Closed Jackson networks: state space, routing, traffic and balance equations, marginals, Buzen's normalizing constants
-- statement:
--   A **closed Jackson network** (§4.3) has $k$ nodes and a fixed population of $N$ customers that circulate forever: there are no external arrivals ($\gamma_i = 0$) and no departures ($r_{i0} = 0$). This module fixes the vocabulary of the chapter's closed-network results.
--
--   1. The **state space** is the finite set of vectors $\bar n = (n_1, \dots, n_k)$ of nonnegative integers with $n_1 + \cdots + n_k = N$.
--   2. A **routing matrix** $R = (r_{ij})$ has entries $r_{ij} \ge 0$ with $\sum_j r_{ij} = 1$ for every $i$; it is **irreducible** if every node can be reached from every node through steps $i \to j$ with $r_{ij} > 0$.
--   3. The **traffic equations** (4.16): $\mu_i\rho_i = \sum_{j=1}^{k} \mu_j r_{ji}\rho_j$ for all $i$; and the **visit-ratio equations** (4.25): $v_i = \sum_{j=1}^{k} v_j r_{ji}$.
--   4. Writing $\bar n; i^+ j^-$ for the state with one more customer at node $i$ and one fewer at node $j$ (Table 4.2), the **flow-balance equations** (4.14) of the single-server network at state $\bar n$ are
--   $$\sum_{j=1}^{k}\sum_{\substack{i=1\\ i\ne j}}^{k} \mu_i r_{ij}\, p_{\bar n; i^+ j^-} = \sum_{i=1}^{k} \mu_i (1 - r_{ii})\, p_{\bar n},$$
--   where, as in the book (p.188), a term with a negative subscript ($n_j = 0$) and a term $\mu_i$ with $n_i = 0$ are zero. A **steady-state distribution** of the $N$-customer network is a probability distribution on the state space that satisfies these equations at every state.
--   5. For a distribution $p$ on the $N$-customer states: the **marginal** $p_i(m; N) = \Pr\{N_i = m\}$, the **complementary marginal** $\bar P_i(m; N) = \Pr\{N_i \ge m\}$, the **throughput** $\lambda_i(N) = \bar P_i(1; N)\,\mu_i$ (server-busy probability times service rate), and the **mean number** $L_i(N) = \sum_{\bar n} n_i\, p_{\bar n}$.
--   6. The multiserver factor (4.13) for a node with $c$ servers, $a(n) = n!$ for $n < c$ and $a(n) = c^{\,n-c}c!$ for $n \ge c$; Buzen's factors $f_i(n) = \rho_i^{\,n}/a_i(n)$; the **normalizing constant** (4.19) $G(N) = \sum_{n_1+\cdots+n_k = N}\prod_{i=1}^{k} f_i(n_i)$; Buzen's auxiliary function (4.20) $g_m(n) = \sum_{n_1+\cdots+n_m=n}\prod_{i=1}^{m} f_i(n_i)$ over the first $m$ nodes; and the **product form** $p_{\bar n} = G(N)^{-1}\prod_{i=1}^{k} f_i(n_i)$ on the $N$-customer states, which is (4.15) for $f_i(n) = \rho_i^{\,n}$ and (4.17) for $f_i(n) = \rho_i^{\,n}/a_i(n)$.
--
--   These objects are shared by every closed-network statement of the chapter: the product form, Buzen's algorithm, the marginal formulas and mean-value analysis.
--
--   **Formalization Note** Nodes are indexed by `Fin k`, so the book's node $i$ is index $i-1$. A distribution is a function on all of $\mathbb N^k$ that vanishes off the $N$-customer states. $g_m$ is defined by the sum (4.20), not by the recursion (4.21), and $g_0(n)$ is $1$ for $n = 0$ and $0$ otherwise.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.188, Table 4.2 and the convention of Eq. (4.9); p.191, Eq. (4.13); pp.195–197, §4.3, Eqs. (4.14)–(4.19); p.199, Eq. (4.20); p.202, Eq. (4.25); pp.208–209, the definitions of p_i(n_i; N), P̄_i(n_i; N) and λ_i(N)

import Mathlib

namespace QueueingFundamentals.Networks

open Finset

/-- The state space of a closed network of `k` nodes with `N` customers (§4.3, p.196):
all `n̄ = (n_1, …, n_k)` with `n_i ∈ ℕ` and `n_1 + ⋯ + n_k = N`. Nodes are indexed by `Fin k`
(book node `i` is index `i - 1`). -/
def states (k N : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset fun _ : Fin k => Finset.range (N + 1)).filter fun n => ∑ i, n i = N

/-- A routing matrix of a closed network (§4.3, p.195: `γ_i = 0`, `r_i0 = 0`): the entries
`r_ij` are routing probabilities, `r_ij ≥ 0`, and each row sums to one. -/
def IsRoutingMatrix {k : ℕ} (R : Fin k → Fin k → ℝ) : Prop :=
  (∀ i j, 0 ≤ R i j) ∧ ∀ i, ∑ j, R i j = 1

/-- The routing matrix is irreducible (p.196): every node can be reached from every node
through routing steps of positive probability. -/
def IsIrreducible {k : ℕ} (R : Fin k → Fin k → ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun a b => 0 < R a b) i j

/-- The traffic equations (4.16), p.196, of a closed network:
`μ_i ρ_i = ∑_{j=1}^{k} μ_j r_ji ρ_j` for every node `i`. -/
def IsTrafficSolution {k : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (rho : Fin k → ℝ) : Prop :=
  ∀ i, mu i * rho i = ∑ j, mu j * R j i * rho j

/-- The visit-ratio equations (4.25), p.202: `v_i = ∑_{j=1}^{k} v_j r_ji` for every node `i`. -/
def IsVisitRatio {k : ℕ} (R : Fin k → Fin k → ℝ) (v : Fin k → ℝ) : Prop :=
  ∀ i, v i = ∑ j, v j * R j i

/-- The state `n̄; i⁺j⁻` of Table 4.2, p.188: one more customer at node `i`, one fewer at node `j`
(used only for `i ≠ j` and `n_j ≥ 1`). -/
def moveState {k : ℕ} (n : Fin k → ℕ) (i j : Fin k) : Fin k → ℕ :=
  Function.update (Function.update n j (n j - 1)) i (n i + 1)

/-- The steady-state flow-balance equations (4.14), p.196, of a closed Jackson network with a
single exponential server of rate `μ_i` at each node, at the state `n̄`:
`∑_{j=1}^{k} ∑_{i ≠ j} μ_i r_ij p_{n̄;i⁺j⁻} = ∑_{i=1}^{k} μ_i (1 − r_ii) p_{n̄}`,
with the book's convention (p.188) that terms with a negative subscript and terms `μ_i` with
`n_i = 0` are zero. -/
def BalanceAt {k : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (p : (Fin k → ℕ) → ℝ)
    (n : Fin k → ℕ) : Prop :=
  (∑ j, ∑ i ∈ univ.filter (fun i => i ≠ j),
      if 1 ≤ n j then mu i * R i j * p (moveState n i j) else 0) =
    ∑ i, if 1 ≤ n i then mu i * (1 - R i i) * p n else 0

/-- A steady-state distribution of the `N`-customer closed Jackson network with single servers
(§1.9 and §4.3): a probability distribution on the states with `n_1 + ⋯ + n_k = N` (zero
elsewhere) that satisfies the balance equations (4.14) at every such state. -/
def IsClosedSteadyState {k : ℕ} (mu : Fin k → ℝ) (R : Fin k → Fin k → ℝ) (N : ℕ)
    (p : (Fin k → ℕ) → ℝ) : Prop :=
  (∀ n, 0 ≤ p n) ∧ (∀ n, n ∉ states k N → p n = 0) ∧ (∑ n ∈ states k N, p n) = 1 ∧
    ∀ n ∈ states k N, BalanceAt mu R p n

/-- The marginal probability `p_i(m; N) = Pr{N_i = m | N customers in network}` (p.208) of a
distribution `p` on the `N`-customer states. -/
noncomputable def marginal {k : ℕ} (N : ℕ) (p : (Fin k → ℕ) → ℝ) (i : Fin k) (m : ℕ) : ℝ :=
  ∑ n ∈ (states k N).filter (fun n => n i = m), p n

/-- The complementary marginal `P̄_i(m; N) = Pr{N_i ≥ m | N customers in network}` (p.208). -/
noncomputable def tailMarginal {k : ℕ} (N : ℕ) (p : (Fin k → ℕ) → ℝ) (i : Fin k) (m : ℕ) : ℝ :=
  ∑ n ∈ (states k N).filter (fun n => m ≤ n i), p n

/-- The throughput of node `i` (p.209): `λ_i(N) = Pr{server busy at node i} · μ_i = P̄_i(1; N) μ_i`. -/
noncomputable def throughput {k : ℕ} (mu : Fin k → ℝ) (N : ℕ) (p : (Fin k → ℕ) → ℝ)
    (i : Fin k) : ℝ :=
  tailMarginal N p i 1 * mu i

/-- The mean number `L_i(N) = ∑_n n p_i(n; N)` of customers at node `i` (p.201, p.204). -/
noncomputable def meanNumber {k : ℕ} (N : ℕ) (p : (Fin k → ℕ) → ℝ) (i : Fin k) : ℝ :=
  ∑ n ∈ states k N, (n i : ℝ) * p n

/-- The multiserver factor `a_i(n_i)` of (4.13), p.191, for a node with `c` servers:
`a(n) = n!` for `n < c` and `a(n) = c^{n−c} c!` for `n ≥ c`. For `c = 1` it is identically `1`. -/
noncomputable def serverFactor (c n : ℕ) : ℝ :=
  if n < c then (n.factorial : ℝ) else (c : ℝ) ^ (n - c) * (c.factorial : ℝ)

/-- Buzen's factors `f_i(n_i) = ρ_i^{n_i} / a_i(n_i)` (p.198) for a closed network with `c_i`
servers at node `i`. -/
noncomputable def buzenFactor {k : ℕ} (rho : Fin k → ℝ) (c : Fin k → ℕ) (i : Fin k) (n : ℕ) : ℝ :=
  rho i ^ n / serverFactor (c i) n

/-- The normalizing constant (4.18)/(4.19), p.197–198:
`G(N) = ∑_{n_1+⋯+n_k=N} ∏_{i=1}^{k} f_i(n_i)`. -/
noncomputable def normConst {k : ℕ} (f : Fin k → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ states k N, ∏ i, f i (n i)

/-- Buzen's auxiliary function (4.20), p.199, over the first `m ≤ k` nodes:
`g_m(n) = ∑_{n_1+⋯+n_m=n} ∏_{i=1}^{m} f_i(n_i)`. For `m = 0` it is `1` at `n = 0` and `0` otherwise
(the empty network). -/
noncomputable def gBuzen {k : ℕ} (f : Fin k → ℕ → ℝ) (m : ℕ) (hm : m ≤ k) (n : ℕ) : ℝ :=
  ∑ x ∈ states m n, ∏ i : Fin m, f (Fin.castLE hm i) (x i)

/-- The product-form distribution (4.15)/(4.17), p.196: `p_{n̄} = (1/G(N)) ∏_{i=1}^{k} f_i(n_i)` on
the states with `n_1 + ⋯ + n_k = N`, and `0` elsewhere. With `f_i(n) = ρ_i^n` it is (4.15), with
`f_i(n) = ρ_i^n / a_i(n)` it is (4.17). -/
noncomputable def productForm {k : ℕ} (f : Fin k → ℕ → ℝ) (N : ℕ) (n : Fin k → ℕ) : ℝ :=
  if n ∈ states k N then (∏ i, f i (n i)) / normConst f N else 0

end QueueingFundamentals.Networks


