-- Prove2me | Definitions.Def_ConstrainedQueueing_MaxThroughput_Model
-- name    : ConstrainedQueueing_MaxThroughput_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:20.80059+00:00
-- url     : https://prove2.me/theorems/043a2a2f-7831-4700-8f6e-2da12a5732c1
-- title:
--   The constrained queueing network of §II, policy π₀, the set C′ and the stability regions C_π, C (pp. 1937–1940)
-- statement:
--   A **constrained queueing network** has $L$ nodes, $N$ servers (links) and $J$ customer classes. Server $i$ takes customers from its origin node $q(i)$ to its destination node $h(i)$. Customers of class $j$ leave the network on reaching a node of the destination set $V_j$, so a **queue** is a pair $(l,j)$ with $l\notin V_j$. The **constraint set** $S$ is a family of sets of servers (activation sets) that may be active together, and $m_i$ is the probability that a customer served by server $i$ in a slot completes service. Standing assumptions used by the theorems (not built into the structure): **C.1**, every subset of an activation set is an activation set; **C.2**, from every node $l\notin V_j$ a chain of servers $i_1,\dots,i_n$ with $q(i_1)=l$, $h(i_m)=q(i_{m+1})$ and $h(i_n)\in V_j$ exists.
--
--   **States and activation rules.** A state $x$ gives the length $x_{lj}\in\mathbb N$ of every queue; $x_{lj}$ is read as $0$ when $l\in V_j$. A **multiclass activation vector** assigns to each server either a class it serves or idleness, such that the set of active servers lies in $S$. An **activation rule** $g$ maps states to multiclass activation vectors and never activates servers for nonexisting customers: for every node $l$ and class $j$, at most $x_{lj}$ servers $i$ with $q(i)=l$ serve class $j$. The class $H$ of stationary policies is the class of activation rules.
--
--   **Dynamics (2.1).** Arrivals $A_{lj}$ at queue $(l,j)$ have law $\alpha_{lj}$ on $\mathbb N$, service outcomes $M_i\in\{0,1\}$ are Bernoulli$(m_i)$, all independent, i.i.d. over slots. An arrival law is **admissible** if every $E[A_{lj}^2]<\infty$, and $a_{lj}=E[A_{lj}]$ is its rate. Under rule $g$, queue $(l,j)$ moves from $x_{lj}$ to
--   $$x_{lj}-\#\{i: q(i)=l,\ g(x)_i=j,\ M_i=1\}+\#\{i: h(i)=l,\ g(x)_i=j,\ M_i=1\}+A_{lj},$$
--   which defines the transition matrix $P_{g,\alpha}$ of the queue-length chain.
--
--   **Policy $\pi_0$.** With $D_{ij}(x)=(x_{q(i)j}-x_{h(i)j})m_i$ if $h(i)\notin V_j$ and $D_{ij}(x)=x_{q(i)j}m_i$ if $h(i)\in V_j$, a rule $g$ is a $\pi_0$ rule if for every state $x$ there are a maximizing class $\hat\jmath_i\in\arg\max_j D_{ij}(x)$ for each server, an activation set $\hat c\in\arg\max_{c\in S}\sum_{i\in c}D_{i\hat\jmath_i}(x)$, and $g(x)_i=\hat\jmath_i$ exactly when $i\in\hat c$ and $x_{q(i)\hat\jmath_i}$ exceeds the number of servers $i'$ with $q(i')=q(i)$; otherwise server $i$ is idle. Ties are broken arbitrarily.
--
--   **Flows and $C'$.** A family $f=(f_{ij})\ge 0$ is an **$a$-admissible multicommodity flow** if it satisfies flow conservation (3.5), $a_{lj}=\sum_{i:q(i)=l}f_{ij}-\sum_{i:h(i)=l}f_{ij}$ at every queue $(l,j)$, and carries no class-$j$ flow out of a node of $V_j$. Its total flow is $\hat f_i=\sum_j f_{ij}$. With $\mathrm{co}(S)$ the convex hull of the 0/1 indicator vectors of the activation sets,
--   $$C'=\{a\ge 0:\ \exists f\in F_a,\ c\in\mathrm{co}(S),\ m_i^{-1}\hat f_i<c_i \text{ if } \hat f_i>0,\ \hat f_i=0 \text{ if } c_i=0\}.$$
--
--   **Stability regions.** $C_g$ is the set of rate vectors $a\ge0$ such that the chain $P_{g,\alpha}$ is stable (Definition 3.1) for every admissible arrival law $\alpha$ with rates $a$ (Definition 3.2), and $C=\bigcup_{g\in H}C_g$ (Definition 3.4).
--
--   **Formalization Note.** Nodes, servers and classes are $0$-based. A multiclass activation vector is a map from servers to an optional class (each server serves at most one class). Arrival-rate vectors are indexed by the queues $(l,j)$, $l\notin V_j$; flows out of destination nodes are set to zero because those rows of (3.5) have no queue and no arrivals. A server with $q(i)=h(i)$ contributes $0$ to its own queue. $C'$, $C_g$ are intersected with $a\ge0$; $C_g$ quantifies over every admissible law with the given rates. $\pi_0$ is a predicate on rules, so statements hold for every tie-break. Definition 3.4 prints $\bigcup_{\pi\in G}$; it is read as $H$.
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), pp. 1937–1938, §II (C.1, (2.1), C.2); p. 1939, Definitions 3.2–3.4 and policy π₀; p. 1940, (3.5) and C′

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain

open scoped ENNReal

namespace ConstrainedQueueing.MaxThroughput

/-! The constrained queueing model of Tassiulas–Ephremides 1992, §II (pp. 1937–1938), the policy
`π₀` (§III.B, p. 1939), the set `C′` (§III.C, p. 1940) and the stability regions
(Definitions 3.2 and 3.4, p. 1939). Nodes are `Fin L`, servers `Fin N`, classes `Fin J`
(0-based, where the paper counts from 1). -/

/-- The network data: server `i` takes customers from its origin node `q i` to its destination node
`h i`; class `j` leaves the network on reaching a node of `V j`; `S` is the constraint set (the
activation sets, as sets of servers); `m i` is the probability that a customer served by server `i`
completes service in a slot. -/
structure Network (L N J : ℕ) where
  q : Fin N → Fin L
  h : Fin N → Fin L
  V : Fin J → Finset (Fin L)
  S : Set (Finset (Fin N))
  m : Fin N → ℝ

variable {L N J : ℕ}

/-- Assumption **C.1** (p. 1937): every subset of an activation set is an activation set. -/
def C1 (net : Network L N J) : Prop :=
  ∀ c ∈ net.S, ∀ d ⊆ c, d ∈ net.S

/-- Assumption **C.2** (p. 1938), topological reading: from every node `l` that is not a destination
of class `j` there is a nonempty chain of servers `i₁, …, iₙ` with `q i₁ = l`,
`h i_m = q i_{m+1}`, and `h iₙ ∈ V j`, so a class-`j` customer at `l` can be forwarded to a
destination node of class `j`. -/
def C2 (net : Network L N J) : Prop :=
  ∀ (j : Fin J) (l : Fin L), l ∉ net.V j →
    ∃ path : List (Fin N), ∃ hne : path ≠ [],
      net.q (path.head hne) = l ∧
      path.IsChain (fun i i' => net.h i = net.q i') ∧
      net.h (path.getLast hne) ∈ net.V j

/-- The queues: a pair `(l, j)` is a queue iff node `l` is not a destination of class `j`
(p. 1937: customers of class `j` reaching a node of `V j` leave the system). -/
def QIdx (net : Network L N J) : Type :=
  {p : Fin L × Fin J // p.1 ∉ net.V p.2}

instance (net : Network L N J) : Fintype (QIdx net) := by
  unfold QIdx; infer_instance

instance (net : Network L N J) : DecidableEq (QIdx net) := by
  unfold QIdx; infer_instance

/-- The queue length of class `j` at node `l` in the state `x`, extended by `0` where `(l, j)` is not
a queue (`l ∈ V j`: there are no customers of class `j` at its own destination). -/
def xval (net : Network L N J) (x : QIdx net → ℕ) (l : Fin L) (j : Fin J) : ℕ :=
  if h : l ∉ net.V j then x ⟨(l, j), h⟩ else 0

/-- A multiclass activation vector, encoded by the class each server serves: `e i = some j` iff
`e_ij = 1`, and `e i = none` iff server `i` is idle. -/
abbrev MultiAct (N J : ℕ) := Fin N → Option (Fin J)

/-- `e` is a multiclass activation vector (p. 1937): the set of active servers, `∑_j e^j`,
lies in `S`. -/
def IsMultiAct (net : Network L N J) (e : MultiAct N J) : Prop :=
  (Finset.univ.filter fun i => (e i).isSome) ∈ net.S

/-- An activation rule (p. 1938): a map `g` from states to multiclass activation vectors such that no
servers are activated for nonexisting customers: for every node `l` and class `j`, the number of
servers `i` with `q i = l` activated for class `j` is at most `x_{lj}`. The class `H` of stationary
policies is the class of such rules. -/
def IsActivationRule (net : Network L N J) (g : (QIdx net → ℕ) → MultiAct N J) : Prop :=
  ∀ x, IsMultiAct net (g x) ∧
    ∀ (l : Fin L) (j : Fin J),
      (Finset.univ.filter fun i => net.q i = l ∧ g x i = some j).card ≤ xval net x l j

/-- The law of the arrivals: `α p` is the distribution of `A_lj(t)` for the queue `p = (l, j)`. -/
abbrev ArrivalLaw (net : Network L N J) := QIdx net → PMF ℕ

/-- The standing moment assumption: every arrival law has a finite second moment
`E[A_lj(t)^2] < ∞`. -/
def Admissible {net : Network L N J} (α : ArrivalLaw net) : Prop :=
  ∀ p, Summable (fun k : ℕ => (k : ℝ) ^ 2 * (α p k).toReal)

/-- The arrival rate `a_lj = E[A_lj(t)]` of queue `p = (l, j)`. -/
noncomputable def meanRate {net : Network L N J} (α : ArrivalLaw net) : QIdx net → ℝ :=
  fun p => ∑' k : ℕ, (k : ℝ) * (α p k).toReal

/-- The dynamics (2.1), queue by queue: from the state `x`, under the activation vector `g x`, with
service outcomes `M i ∈ {0, 1}` and arrivals `A`, queue `p = (l, j)` loses the class-`j` customers
whose service at a server with `q i = l` completes, gains those completing at a server with
`h i = l`, and gains the `A p` new arrivals. -/
def nextState (net : Network L N J) (g : (QIdx net → ℕ) → MultiAct N J) (x : QIdx net → ℕ)
    (A : QIdx net → ℕ) (M : Fin N → Bool) : QIdx net → ℕ :=
  fun p =>
    x p - (Finset.univ.filter fun i => net.q i = p.1.1 ∧ g x i = some p.1.2 ∧ M i = true).card
      + (Finset.univ.filter fun i => net.h i = p.1.1 ∧ g x i = some p.1.2 ∧ M i = true).card
      + A p

/-- Probability of the service outcome vector `M`: the `M i` are independent Bernoulli variables with
`P(M i = 1) = m i`. -/
noncomputable def serviceProb (net : Network L N J) (M : Fin N → Bool) : ℝ≥0∞ :=
  ∏ i, if M i then ENNReal.ofReal (net.m i) else ENNReal.ofReal (1 - net.m i)

/-- Probability of the arrival vector `A`: the arrivals at different queues are independent, queue
`p` with law `α p`. -/
noncomputable def arrivalProb {net : Network L N J} (α : ArrivalLaw net) (A : QIdx net → ℕ) :
    ℝ≥0∞ :=
  ∏ p, α p (A p)

open Classical in
/-- The transition matrix of the queue-length chain under the stationary activation rule `g`
(p. 1938): `P(X(t+1) = y | X(t) = x)`, with arrivals and service outcomes of slot `t + 1` independent
of each other and of the past, arrivals `A ~ ⊗_p α p` and services `M ~ ⊗_i Bernoulli(m i)`. -/
noncomputable def transProb (net : Network L N J) (g : (QIdx net → ℕ) → MultiAct N J)
    (α : ArrivalLaw net) (x y : QIdx net → ℕ) : ℝ≥0∞ :=
  ∑' A : QIdx net → ℕ, ∑ M : Fin N → Bool,
    arrivalProb α A * serviceProb net M * (if nextState net g x A M = y then 1 else 0)

/-- The weight `D_ij` of stage 1 of `π₀` (p. 1939), as a function of the state `x = X(t − 1)`:
`(x_{q(i)j} − x_{h(i)j}) m_i` if `h(i) ∉ V_j`, and `x_{q(i)j} m_i` if `h(i) ∈ V_j`. -/
noncomputable def D (net : Network L N J) (x : QIdx net → ℕ) (i : Fin N) (j : Fin J) : ℝ :=
  if net.h i ∉ net.V j then
    ((xval net x (net.q i) j : ℝ) - (xval net x (net.h i) j : ℝ)) * net.m i
  else (xval net x (net.q i) j : ℝ) * net.m i

/-- `g` is an activation rule of policy `π₀` (p. 1939), with ties in stages 1–3 broken arbitrarily:
for every state `x` there are a choice `ĵ i` of a class maximizing `D_ij` (stage 1, so
`D_i = D_{iĵ_i}`), an activation set `ĉ ∈ S` maximizing `∑_{i ∈ c} D_i` over `c ∈ S` (stage 2),
and `g x i = ĵ i` exactly when `i ∈ ĉ` and `x_{q(i)ĵ_i}` exceeds the number of servers that serve
queue `q(i)` (stage 3); otherwise server `i` is idle. -/
def IsPi0Rule (net : Network L N J) (g : (QIdx net → ℕ) → MultiAct N J) : Prop :=
  ∀ x, ∃ jhat : Fin N → Fin J,
    (∀ i j, D net x i j ≤ D net x i (jhat i)) ∧
    ∃ chat ∈ net.S,
      (∀ c ∈ net.S, ∑ i ∈ c, D net x i (jhat i) ≤ ∑ i ∈ chat, D net x i (jhat i)) ∧
      ∀ i, g x i =
        if i ∈ chat ∧
            (Finset.univ.filter fun i' => net.q i' = net.q i).card < xval net x (net.q i) (jhat i)
        then some (jhat i) else none

/-- `f = (f_ij)` is an `a`-admissible multicommodity flow (p. 1940): `f ≥ 0`, and the flow
conservation equations (3.5) `a^j = −R^j f^j` hold at every queue `(l, j)`:
`a_lj = ∑_{i : q(i) = l} f_ij − ∑_{i : h(i) = l} f_ij`; moreover no class-`j` flow leaves a
destination node of class `j` (the rows `l ∈ V j` of (3.5), where class `j` has no queue and no
arrivals). -/
def IsAdmissibleFlow (net : Network L N J) (a : QIdx net → ℝ) (f : Fin N → Fin J → ℝ) : Prop :=
  (∀ i j, 0 ≤ f i j) ∧
    (∀ p : QIdx net,
      a p = (∑ i ∈ Finset.univ.filter (fun i => net.q i = p.1.1), f i p.1.2)
        - ∑ i ∈ Finset.univ.filter (fun i => net.h i = p.1.1), f i p.1.2) ∧
    ∀ i j, net.q i ∈ net.V j → f i j = 0

/-- The total flow vector `f̂ = ∑_j f^j`. -/
def fhat (f : Fin N → Fin J → ℝ) (i : Fin N) : ℝ :=
  ∑ j, f i j

/-- The 0/1 activation vector of an activation set. -/
def actVec (c : Finset (Fin N)) : Fin N → ℝ :=
  fun i => if i ∈ c then 1 else 0

/-- `co(S)`, the convex hull of the constraint set. -/
def coS (net : Network L N J) : Set (Fin N → ℝ) :=
  convexHull ℝ (actVec '' net.S)

/-- The set `C′` (p. 1940): the nonnegative rate vectors `a` with an `a`-admissible flow `f` and a
`c ∈ co(S)` such that `m_i⁻¹ f̂_i < c_i` whenever `f̂_i > 0`, and `f̂_i = 0` whenever `c_i = 0`. -/
def Cprime (net : Network L N J) : Set (QIdx net → ℝ) :=
  {a | (∀ p, 0 ≤ a p) ∧ ∃ f, IsAdmissibleFlow net a f ∧ ∃ c ∈ coS net,
    ∀ i, (0 < fhat f i → fhat f i / net.m i < c i) ∧ (c i = 0 → fhat f i = 0)}

/-- The stability region `C_g` of the stationary policy with activation rule `g` (Definition 3.2,
p. 1939): the nonnegative rate vectors `a` such that the queue-length chain is stable under `g` for
every arrival law with finite second moments and mean `a`. -/
def stabRegion (net : Network L N J) (g : (QIdx net → ℕ) → MultiAct N J) : Set (QIdx net → ℝ) :=
  {a | (∀ p, 0 ≤ a p) ∧
    ∀ α : ArrivalLaw net, Admissible α → meanRate α = a → IsStable (transProb net g α)}

/-- The stability region of the system (Definition 3.4, p. 1939): `C = ⋃_{π ∈ H} C_π`, the union
over all activation rules. -/
def sysStabRegion (net : Network L N J) : Set (QIdx net → ℝ) :=
  ⋃ g ∈ {g | IsActivationRule net g}, stabRegion net g

end ConstrainedQueueing.MaxThroughput


