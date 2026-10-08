-- Prove2me | Definitions.Def_ConstrainedQueueing_Nonstationary_Model
-- name    : ConstrainedQueueing_Nonstationary_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:29.40085+00:00
-- url     : https://prove2.me/theorems/f1f6eaf4-9e3c-4201-86b9-3aec55152732
-- title:
--   §II–§IV, pp. 1937–1941 — single-class constrained queueing network, co(S), C′, cuts of N_af, history-dependent policies, runs of (2.1)
-- statement:
--   This file fixes the single-class constrained queueing system of §IV and the flow network used in the proof of its main theorem.
--
--   **Network.** There are $L$ queues and $N$ servers (links). Server $i$ serves queue $q(i)$ and sends each customer it serves either to a queue $h(i)$ or out of the system (to a destination node, where customers are not queued). The **constraint set** $S$ is a family of **activation sets**: sets of servers that may be activated in the same slot. Assumption **C.1** says that every subset of an activation set is an activation set. The **activation vector** of a set $c$ of servers is the binary vector $\mathbf 1_c\in\{0,1\}^N$, and $\mathrm{co}(S)$ is the convex hull of the activation vectors of the sets in $S$.
--
--   **Routing matrix and admissible flows.** The routing matrix $R$ is the $L\times N$ matrix with $r_{li}=1$ if $h(i)=l$, $r_{li}=-1$ if $q(i)=l$, and $r_{li}=0$ otherwise (a server with $q(i)=h(i)=l$ gets $1-1=0$). For a rate vector $a\in\mathbb R^L$, a vector $f\in\mathbb R^N$ is an **$a$-admissible flow** if
--   $$f\ge 0,\qquad a=-Rf, \tag{3.5}$$
--   that is, at each queue the exogenous rate equals the outgoing flow minus the incoming flow.
--
--   **The set $C'$.** With one class and one-slot service times ($m_i=1$),
--   $$C'=\{a\ge 0:\ \exists f \text{ $a$-admissible},\ \exists c\in\mathrm{co}(S),\ \forall i,\ (f_i>0\Rightarrow f_i<c_i)\ \text{and}\ (c_i=0\Rightarrow f_i=0)\}.$$
--   Its closure is written $\bar C'$.
--
--   **The flow network $N_{af}$.** Its nodes are the $L$ queues, an originator $o$ and a terminal $d$. There is one edge $(o,l)$ of capacity $a_l$ for each queue $l$, and one edge per server $k$, of capacity $f_k$, from $q(k)$ to $h(k)$, or to $d$ if server $k$ sends traffic out of the system (parallel servers give parallel edges). A **cut** $(W,W')$ is a partition of the nodes with $o\in W$, $d\in W'$; it is determined by the set $W$ of queues on the originator's side. Its capacity is the total capacity of the edges directed from $W$ to $W'$:
--   $$C_{af}((W,W'))=\sum_{l\notin W}a_l+\sum_{k:\ q(k)\in W,\ h(k)\notin W}f_k ,$$
--   where "$h(k)\notin W$" includes the servers that send traffic out of the system. A **mincut** is a cut of minimum capacity, and $C_{af}((W,W')_{af})$ is the minimum cut capacity.
--
--   **Policies and runs.** A **history-dependent policy** $\pi=\{g_t\}$ (the class $\tilde G$) chooses the activation set $E(t+1)$ of slot $t+1$ as a function of the queue-length vectors $X(0),\dots,X(t)$. It is **admissible** if every chosen set lies in $S$ and, as for every activation rule of §II, no server is activated for nonexisting customers: the number of chosen servers of queue $l$ is at most the current length of queue $l$. Given arrivals $A_l(t+1)$ in slot $t+1$, the queue-length process obeys (2.1) with one class and $M\equiv I$:
--   $$X_l(t+1)=X_l(t)-\#\{i\in E(t+1):q(i)=l\}+\#\{i\in E(t+1):h(i)=l\}+A_l(t+1).$$
--
--   These objects are shared by every statement of the mission: Lemma 3.1 (closure of $C'$), Lemma 4.1 and Corollary 4.1 (mincuts of $N_{af}$ outside $\bar C'$), the pathwise bound (4.7), and Theorem 4.1.
--
--   **Formalization Note.** Queues are `Fin L` and servers `Fin N`, indexed from 0 (the paper counts from 1). A server's destination is `h i : Option (Fin L)`, `none` meaning "out of the system". The constraint set is `S : Set (Finset (Fin N))`; C.1 is the predicate `C1`, and the theorems add $\emptyset\in S$ as a hypothesis (the idle set is always an activation set; without it $S$ may be empty and no policy exists). $C'$ includes $a\ge 0$ (the paper's rate vectors are nonnegative; without it, negative vectors satisfy $a=-Rf$). A cut is encoded by `W : Finset (Fin L)` and `IsMinCut` says it has minimum capacity; `minCutCap` is the minimum over all `W`. A policy is `π t : (Fin (t+1) → Fin L → ℕ) → Finset (Fin N)`; `π t` sees $X(0),\dots,X(t)$ and returns $E(t+1)$. In `IsRun`, `A t` are the arrivals of slot $t+1$ and `X t` is the state at the end of slot $t$; (2.1) is written in $\mathbb N$, and the subtraction never truncates for an admissible policy (checked in the mission's sanity file).
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), pp. 1937–1938 (§II: activation sets, C.1, activation rules, (2.1), routing matrix), p. 1940 (§III.C: (3.5), F_a, C′), p. 1941 (§IV: class G̃, network N_af, cuts, mincut)

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model

namespace ConstrainedQueueing.Nonstationary

/-- A single-class constrained queueing network (Tassiulas–Ephremides 1992, §II, pp. 1937–1938,
specialised to one customer class as in §IV, p. 1941).

* The `L` queues are `Fin L` and the `N` servers (links) are `Fin N` (the paper counts from 1).
* `q i` is the queue served by server `i` (its origin node `q(i)`).
* `h i = some l` means that server `i` directs the customers it serves to queue `l`;
  `h i = none` means that it directs them out of the system (its destination node `h(i)` is a
  destination of the unique class, where customers are not queued).
* `S` is the constraint set: the activation sets, each a set of servers that can be activated in
  the same slot. -/
structure Network (L N : ℕ) where
  /-- origin queue `q(i)` of server `i` -/
  q : Fin N → Fin L
  /-- destination of server `i`: `some l` for queue `l`, `none` for out of the system -/
  h : Fin N → Option (Fin L)
  /-- the constraint set `S` of activation sets -/
  S : Set (Finset (Fin N))

variable {L N : ℕ}

/-- Assumption C.1 (p. 1937): every subset of an activation set is an activation set. -/
def C1 (net : Network L N) : Prop :=
  ∀ c ∈ net.S, ∀ d ⊆ c, d ∈ net.S

/-- `co(S)`: the convex hull of the activation vectors of the constraint set (p. 1940). -/
def coS (net : Network L N) : Set (Fin N → ℝ) :=
  convexHull ℝ (ConstrainedQueueing.MaxThroughput.actVec '' net.S)

/-- The routing matrix `R` of the unique class (p. 1938): `r_{li} = 1` if `h(i) = l`,
`r_{li} = -1` if `q(i) = l`, and `0` otherwise. A server with `q(i) = l` and `h(i) = l`
(a self-loop) gets `1 - 1 = 0`. -/
def routing (net : Network L N) : Matrix (Fin L) (Fin N) ℝ :=
  fun l i => (if net.h i = some l then 1 else 0) - (if net.q i = l then 1 else 0)

/-- An `a`-admissible flow vector (p. 1940, (3.5)) for one class: a nonnegative vector `f`
indexed by the servers with `a = -R f`, i.e. at every queue `l` the exogenous rate `a_l` equals
the flow leaving `l` minus the flow entering `l`. -/
def IsAdmissibleFlow (net : Network L N) (a : Fin L → ℝ) (f : Fin N → ℝ) : Prop :=
  0 ≤ f ∧ a = -((routing net).mulVec f)

/-- The set `C'` (p. 1940) for one class and `m_i = 1` (the service times of §IV are one slot):
nonnegative rate vectors `a` for which there are an `a`-admissible flow `f` and a point `c ∈ co(S)`
with `f_i < c_i` whenever `f_i > 0` and `f_i = 0` whenever `c_i = 0`. -/
def Cprime (net : Network L N) : Set (Fin L → ℝ) :=
  {a | 0 ≤ a ∧ ∃ f, IsAdmissibleFlow net a f ∧ ∃ c ∈ coS net,
    ∀ i, (0 < f i → f i < c i) ∧ (c i = 0 → f i = 0)}

/-- The servers whose edge in the flow network `N_af` (p. 1941) is directed from the originator
side `W ∪ {o}` of a cut to the terminal side `(Fin L \ W) ∪ {d}`: server `i` serves a queue in `W`
and directs traffic either out of the system (edge `(q(i), d)`) or to a queue outside `W`. -/
def serverOut (net : Network L N) (W : Finset (Fin L)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => net.q i ∈ W ∧ ∀ l, net.h i = some l → l ∉ W)

/-- The capacity `C_af((W, W'))` of a cut of the flow network `N_af` (p. 1941).

The graph `Y` has one node per queue, an originator `o` and a terminal `d`; one edge `(o, l)` of
capacity `a_l` per queue `l`; and one edge per server `k`, of capacity `f_k`, from `q(k)` to `h(k)`
(to `d` when `h(k) = none`). Parallel servers give parallel edges. A cut `(W, W')` is a partition
of the nodes with `o ∈ W`, `d ∈ W'`; it is determined by the set `W : Finset (Fin L)` of queues on
the originator's side. Its capacity is the sum of the capacities of the edges directed from the
originator side to the terminal side: the edges `(o, l)` with `l ∉ W`, plus the server edges in
`serverOut net W`. -/
def cutCap (net : Network L N) (a : Fin L → ℝ) (f : Fin N → ℝ) (W : Finset (Fin L)) : ℝ :=
  ∑ l ∈ Finset.univ \ W, a l + ∑ i ∈ serverOut net W, f i

/-- `W` (the queues on the originator's side) determines a mincut of `N_af`: a cut of minimum
capacity (p. 1941). -/
def IsMinCut (net : Network L N) (a : Fin L → ℝ) (f : Fin N → ℝ) (W : Finset (Fin L)) : Prop :=
  ∀ W' : Finset (Fin L), cutCap net a f W ≤ cutCap net a f W'

/-- The capacity `C_af((W, W')_af)` of a mincut of `N_af`: the minimum cut capacity over all cuts. -/
def minCutCap (net : Network L N) (a : Fin L → ℝ) (f : Fin N → ℝ) : ℝ :=
  (Finset.univ : Finset (Finset (Fin L))).inf' ⟨∅, Finset.mem_univ _⟩ (cutCap net a f)

/-- A history-dependent (nonstationary) scheduling policy (p. 1941, the class `G̃`): `π t` sees the
queue-length vectors `X(0), …, X(t)` (the whole history up to the end of slot `t`) and returns the
activation set `E(t+1)` used in slot `t+1`. -/
def HistPolicy (L N : ℕ) : Type :=
  (t : ℕ) → (Fin (t + 1) → Fin L → ℕ) → Finset (Fin N)

/-- The number of servers of the set `E` that serve queue `l`. -/
def numServing (net : Network L N) (E : Finset (Fin N)) (l : Fin L) : ℕ :=
  (E.filter (fun i => net.q i = l)).card

/-- The number of servers of the set `E` that direct traffic to queue `l`. -/
def numFeeding (net : Network L N) (E : Finset (Fin N)) (l : Fin L) : ℕ :=
  (E.filter (fun i => net.h i = some l)).card

/-- A policy of the class `G̃` (pp. 1938, 1941): every selected set is an activation set (in `S`),
and, as for every activation rule (p. 1938), no server is activated for nonexisting customers: the
number of activated servers of queue `l` is at most the current length of queue `l`. -/
def IsAdmissiblePolicy (net : Network L N) (π : HistPolicy L N) : Prop :=
  ∀ t (hist : Fin (t + 1) → Fin L → ℕ),
    π t hist ∈ net.S ∧ ∀ l, numServing net (π t hist) l ≤ hist (Fin.last t) l

/-- `X` is the queue-length process of the network under policy `π`, from the initial state `x0`,
for the arrival sequence `A` (equation (2.1), p. 1938, with one class and `M_i(t) = 1`).
`A t l` is the number of arrivals at queue `l` during slot `t + 1`, and `X t` is the
queue-length vector at the end of slot `t`. In slot `t + 1` the activation set is
`E = π t (X 0, …, X t)`, each activated server moves one customer from its queue `q(i)` to `h(i)`,
and the arrivals join:
`X_l(t+1) = X_l(t) - #{i ∈ E : q(i) = l} + #{i ∈ E : h(i) = l} + A_l(t+1)`. -/
def IsRun (net : Network L N) (π : HistPolicy L N) (x0 : Fin L → ℕ) (A : ℕ → Fin L → ℕ)
    (X : ℕ → Fin L → ℕ) : Prop :=
  X 0 = x0 ∧ ∀ t l,
    X (t + 1) l = X t l - numServing net (π t (fun k => X k)) l
      + numFeeding net (π t (fun k => X k)) l + A t l

end ConstrainedQueueing.Nonstationary


