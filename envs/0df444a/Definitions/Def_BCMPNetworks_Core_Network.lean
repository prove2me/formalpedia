-- Prove2me | Definitions.Def_BCMPNetworks_Core_Network
-- name    : BCMPNetworks_Core_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:39:36.102369+00:00
-- url     : https://prove2.me/theorems/39e5f266-3394-46e6-b178-561fefdf2860
-- title:
--   BCMP network data: N centers of types 1–4, R classes, class-switching routing, subchains, Coxian stages, arrival processes
-- statement:
--   A **BCMP network** with $N$ service centers, $R$ customer classes and $m$ routing subchains consists of the following data.
--
--   1. A **type** $t_i \in \{1,2,3,4\}$ for each center $i$: type 1 is first-come-first-served with a single exponential service time of rate $\mu_i$ shared by all classes; type 2 is a single processor-sharing server; type 3 has at least as many servers as customers (infinite server); type 4 is a single preemptive-resume last-come-first-served server.
--   2. A **routing matrix** $P = [p_{i,r;j,s}]$ on pairs (center, class): a class-$r$ customer finishing service at center $i$ next requires center $j$ in class $s$ with probability $p_{i,r;j,s}$, and leaves the network with probability $1-\sum_{j,s} p_{i,r;j,s}$.
--   3. A **subchain labelling** $(i,r) \mapsto k \in \{1,\dots,m\}$, the subchain $E_k$ containing $(i,r)$, and a population $K_k$ used when $E_k$ is closed.
--   4. An **arrival process**: either (A) a single Poisson stream of rate $\lambda(M(S))$ depending on the total number $M(S)$ of customers, or (B) one Poisson stream per subchain, of rate $\lambda_k(M(S/E_k))$; an arrival enters center $j$ in class $s$ with probability $q_{js}$.
--   5. For each class $r$ at a type 2, 3 or 4 center $i$, a **Coxian service time** with $u_{ir} \ge 1$ exponential stages of rates $\mu_{irl}$; after stage $l$ the customer continues to stage $l+1$ with probability $a_{irl}$ and finishes with probability $b_{irl} = 1-a_{irl}$.
--
--   A subchain $E_k$ is **closed** when $q_{js} = 0$ for all $(j,s) \in E_k$; the network is closed when all subchains are. The quantity
--   $$A_{irl} = \prod_{j<l} a_{irj}$$
--   is the probability that a class-$r$ customer at center $i$ reaches stage $l$ (stages numbered from $0$).
--
--   The standing assumptions (`IsValid`) are: $p \ge 0$ and each row of $P$ sums to at most $1$; $p_{i,r;j,s} \ne 0$ only inside one subchain; rows of closed subchains sum to exactly $1$; $q \ge 0$; arrival rates are nonnegative, and $\sum_{j,s} q_{js} = 1$ for process (A) unless the network is closed, while $\sum_{(j,s)\in E_k} q_{js} = 1$ for each open subchain under process (B); $\mu_i > 0$ at type-1 centers; $\mu_{irl} > 0$ at type 2–4 centers; $0 \le a_{irl} \le 1$ and $a$ vanishes at the last stage.
--
--   These data and assumptions are the model of §2 on which every statement of the mission is built.
--
--   **Formalization Note** Stages are indexed from $0$, so the paper's $A_{irl} = \prod_{j=1}^{l} a_{irj}$ (p. 253) becomes $\prod_{j<l} a_{irj}$: the printed product includes one factor too many (the branch out of stage $l$ itself), which makes $A_{ir,u_{ir}} = 0$ and, for exponential service ($u_{ir}=1$), every $f_i$ of a type 2–4 center zero, so the theorem as printed fails. The paper assumes each subchain is an ergodic class of $P$; only the closure of subchains under routing is kept here, which generalizes the model. The state-dependent FCFS rate $\mu_i(j)$ allowed by Condition 1 is not modelled.
-- source:
--   Baskett, Chandy, Muntz, Palacios, Open, Closed, and Mixed Networks of Queues with Different Classes of Customers, J. ACM 22 (1975), pp. 250-251, Sections 2.1-2.2, Fig. 1; p. 253, Section 3.2 (closed subchains, Fig. 3, A_irl)

import Mathlib

namespace BCMPNetworks.Core

/-- The four service-center types of Baskett–Chandy–Muntz–Palacios (1975), §2.1:
type 1 = FCFS with a class-independent exponential service time, type 2 = single-server
processor sharing, type 3 = infinite server (as many servers as customers), type 4 =
single-server preemptive-resume LCFS. -/
inductive CenterType
  | fcfs
  | ps
  | is
  | lcfs
  deriving DecidableEq

/-- The two state-dependent arrival processes of §2.1. `total lam`: one Poisson stream whose
rate `lam (M S)` depends on the total number of customers in the network. `perChain lam`: one
Poisson stream per subchain `k`, whose rate `lam k (M(S/E_k))` depends on the number of
customers of that subchain. -/
inductive ArrivalProcess (m : ℕ)
  | total (lam : ℕ → ℝ)
  | perChain (lam : Fin m → ℕ → ℝ)

/-- The data of a BCMP network with `N` service centers, `R` customer classes and `m` routing
subchains (§2.1–§2.2, §3.2).

* `type i` is the type (1–4) of center `i`;
* `P i r j s` is the probability that a class-`r` customer finishing service at center `i`
  next requires center `j` in class `s`;
* `chain i r` is the subchain `E_k` containing the pair `(i, r)`;
* `K k` is the fixed population of subchain `k` when that subchain is closed;
* `arrival` is the external arrival process and `q j s` the probability that an arrival
  enters center `j` in class `s`;
* `μ i` is the (class-independent) exponential service rate of a type-1 center;
* `u i r` is the number of Coxian stages of the class-`r` service time at center `i`,
  `μs i r l` the rate of stage `l` and `a i r l` the probability of continuing from stage `l`
  to stage `l + 1` (stages are indexed from `0`). -/
structure Network (N R m : ℕ) where
  type : Fin N → CenterType
  P : Fin N → Fin R → Fin N → Fin R → ℝ
  chain : Fin N → Fin R → Fin m
  K : Fin m → ℕ
  arrival : ArrivalProcess m
  q : Fin N → Fin R → ℝ
  μ : Fin N → ℝ
  u : Fin N → Fin R → ℕ+
  μs : (i : Fin N) → (r : Fin R) → Fin (u i r) → ℝ
  a : (i : Fin N) → (r : Fin R) → Fin (u i r) → ℝ

namespace Network

variable {N R m : ℕ} (net : Network N R m)

/-- Subchain `k` is closed when no external arrival ever enters it: `q j s = 0` for every
`(j, s) ∈ E_k` (§3.2, p. 253). -/
def IsClosedChain (k : Fin m) : Prop :=
  ∀ (j : Fin N) (s : Fin R), net.chain j s = k → net.q j s = 0

/-- The network is closed when every subchain is closed. -/
def IsClosedNetwork : Prop :=
  ∀ k : Fin m, net.IsClosedChain k

/-- The probability that a class-`r` customer at center `i` reaches stage `l` of its
Coxian service time: `A_{irl} = ∏_{j < l} a_{irj}` (0-based stages). This is the paper's
`A_{irl}` with the off-by-one misprint of p. 253 corrected. -/
def A (i : Fin N) (r : Fin R) (l : Fin (net.u i r)) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin (net.u i r) => j < l), net.a i r j

/-- The standing assumptions of §2 and §3.2 on the network data. -/
structure IsValid : Prop where
  /-- routing probabilities are nonnegative -/
  P_nonneg : ∀ i r j s, 0 ≤ net.P i r j s
  /-- each row of the routing matrix sums to at most one; the defect is the probability of
  leaving the network -/
  P_row_le_one : ∀ i r, ∑ j, ∑ s, net.P i r j s ≤ 1
  /-- routing never leaves a subchain -/
  P_chain : ∀ i r j s, net.P i r j s ≠ 0 → net.chain i r = net.chain j s
  /-- a customer of a closed subchain never leaves the network -/
  P_row_closed : ∀ i r, net.IsClosedChain (net.chain i r) → ∑ j, ∑ s, net.P i r j s = 1
  /-- arrival routing probabilities are nonnegative -/
  q_nonneg : ∀ j s, 0 ≤ net.q j s
  /-- arrival process (A): nonnegative rates, and the `q` sum to one unless the network is
  closed; arrival process (B): nonnegative rates, and within each open subchain the `q`
  sum to one -/
  arrival_ok :
    match net.arrival with
    | .total lam => (∀ n, 0 ≤ lam n) ∧
        (¬ net.IsClosedNetwork → ∑ j, ∑ s, net.q j s = 1)
    | .perChain lam => (∀ k n, 0 ≤ lam k n) ∧
        (∀ k, ¬ net.IsClosedChain k →
          ∑ j, ∑ s, (if net.chain j s = k then net.q j s else 0) = 1)
  /-- type-1 centers have a positive exponential service rate -/
  μ_pos : ∀ i, net.type i = .fcfs → 0 < net.μ i
  /-- stage rates at type-2, -3, -4 centers are positive -/
  μs_pos : ∀ i r l, net.type i ≠ .fcfs → 0 < net.μs i r l
  /-- continuation probabilities lie in `[0, 1]` -/
  a_nonneg : ∀ i r l, 0 ≤ net.a i r l
  a_le_one : ∀ i r l, net.a i r l ≤ 1
  /-- no continuation after the last stage -/
  a_last : ∀ i r (l : Fin (net.u i r)), l.val + 1 = (net.u i r : ℕ) → net.a i r l = 0

end Network

end BCMPNetworks.Core


