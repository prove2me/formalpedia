-- Prove2me | Definitions.Def_TwoEchelonVRP_Route2
-- name    : TwoEchelonVRP_Route2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:26:36.774992+00:00
-- url     : https://prove2.me/theorems/47f44f34-6dbf-4693-940e-88820aca38e3
-- title:
--   Second-level routes $\mathcal R_k$: load $w_{kl}$, cost $c_{kl}$, visits $a_{ikl}$
-- statement:
--   A **second-level route** of satellite $k \in N_S$ is a simple cycle in $G$ through $k$ and a nonempty set $R_{kl}$ of customers whose total demand does not exceed $Q_2$. It is described by the order $c_0, \dots, c_m$ in which it visits its customers (canonical orientation, see `InjSeq`), i.e. the cycle $k, c_0, \dots, c_m, k$. Since every customer is adjacent to every satellite and every other customer, the set of such customer sequences is the same for every satellite, and $\mathcal R_k$ is indexed by it. Associated with route $l \in \mathcal R_k$ are
--
--   1. its customer set $R_{kl} = \{c_0, \dots, c_m\}$;
--   2. its **load** $w_{kl} = \sum_{i \in R_{kl}} q_i \le Q_2$;
--   3. the coefficient $a_{ikl} \in \{0,1\}$, the number of times customer $i$ is visited by $l$;
--   4. its **cost**
--   $$
--   c_{kl} = d'_{k c_0} + \sum_{j=0}^{m-1} d'_{c_j c_{j+1}} + d'_{c_m k} + H_k\, w_{kl},
--   $$
--   the sum of the (modified) costs of the traversed edges plus the handling cost.
--
--   These are the columns of formulation F and the data of the multiplier condition (12).
--
--   **Formalization Note** Single-customer routes $(k, i, k)$ are included; they traverse the edge $\{k, i\}$ twice and cost $2 d_{ki} + U_2 + H_k q_i$ (the paper's algorithm starts from "all single-customer routes (k, i, k)", §4.1, p. 302). Routes of all satellites are indexed by `Fin ns × Route2 I`. The module declares `Route2` with its `Fintype` instance, `custSet`, `load2`, `aCoef` and `cost2`.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §2, unnumbered, p. 299 (second-level route: simple cycle through a satellite and customers, load ≤ Q_2, cost = traversed edges + U_2, handling cost H_k); §2.1, unnumbered, p. 300 (𝓡_k, 𝓡_ik, R_kl, E(R_kl), w_kl, c_kl); §3.1, p. 301 (a_ikl, below (12))

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_modCost
import Definitions.Def_TwoEchelonVRP_InjSeq

namespace TwoEchelonVRP

/-- **Second-level routes** `𝓡_k`.
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §2, unnumbered, p. 299: a second-level vehicle
"performs a route, that is a simple cycle in G passing through a satellite and a subset of
customers and such that the total demand of the visited customers does not exceed the vehicle
capacity Q_2"; §2.1, p. 300: "Let 𝓡_k be the index set of the second-level routes passing through
satellite k ∈ N_S".

An element of `Route2 I` is a nonempty injective sequence of customers `c 0, …, c m` in canonical
orientation (`InjSeq.IsCanonical`) whose total demand is at most `Q_2`. Paired with a satellite
`k`, it is the cycle `k, c 0, …, c m, k` of `𝓡_k`. Every customer is adjacent to every satellite
and to every other customer, so every such sequence is a cycle of `G`; hence `𝓡_k` is the same
set of customer sequences for every `k`, and the routes of all satellites are indexed by
`Fin ns × Route2 I`.

**Formalization Note.** A route with a single customer, `(k, i, k)`, is included (it traverses the
edge `{k, i}` twice); the paper's algorithm initializes with "all single-customer routes (k, i, k)"
(§4.1, p. 302). -/
def Route2 {ns nc : ℕ} (I : Instance ns nc) : Type :=
  {c : InjSeq nc // c.IsCanonical ∧ ∑ i ∈ c.toFinset, I.q i ≤ I.Q2}

noncomputable instance {ns nc : ℕ} (I : Instance ns nc) : Fintype (Route2 I) := by
  unfold Route2; infer_instance

/-- The set `R_kl` of customers visited by a second-level route `l`
(Baldacci et al., Operations Research 61(2) (2013), §2.1, p. 300). -/
def custSet {ns nc : ℕ} {I : Instance ns nc} (l : Route2 I) : Finset (Fin nc) := l.1.toFinset

/-- The load `w_kl = Σ_{i ∈ R_kl} q_i` of a second-level route
(Baldacci et al., Operations Research 61(2) (2013), §2.1, p. 300). -/
def load2 {ns nc : ℕ} {I : Instance ns nc} (l : Route2 I) : ℕ := ∑ i ∈ custSet l, I.q i

/-- The coefficient `a_ikl`, "the number of times customer i ∈ N_C is visited by route
l ∈ 𝓡_k of satellite k ∈ N_S" (Baldacci et al., Operations Research 61(2) (2013), §3.1, p. 301,
below (12)). Routes are elementary, so it is `1` if `i ∈ R_kl` and `0` otherwise; it does not
depend on `k`. -/
noncomputable def aCoef {ns nc : ℕ} {I : Instance ns nc} (l : Route2 I) (i : Fin nc) : ℝ :=
  if i ∈ custSet l then 1 else 0

/-- The cost `c_kl = Σ_{{i,j} ∈ E(R_kl)} d_ij + H_k w_kl` of route `l` of satellite `k`
(Baldacci et al., Operations Research 61(2) (2013), §2.1, p. 300), with the modified costs
`modCost` of p. 299. For the cycle `k, c 0, …, c m, k` it is
`d'(k, c 0) + Σ_{j < m} d'(c j, c (j+1)) + d'(c m, k) + H_k · w_kl`.

**Formalization Note.** For a single-customer route `(k, i, k)` the edge `{k, i}` is traversed
twice and charged twice, `2 d_ki + U_2 + H_k q_i`, so the route carries the full fixed cost `U_2`. -/
noncomputable def cost2 {ns nc : ℕ} (I : Instance ns nc) (k : Fin ns) (l : Route2 I) : ℝ :=
  modCost I (some (Sum.inl k)) (some (Sum.inr (l.1.2 0)))
    + ∑ j : Fin l.1.1.val, modCost I (some (Sum.inr (l.1.2 j.castSucc))) (some (Sum.inr (l.1.2 j.succ)))
    + modCost I (some (Sum.inr (l.1.2 (Fin.last _)))) (some (Sum.inl k))
    + I.H k * (load2 l : ℝ)

end TwoEchelonVRP


