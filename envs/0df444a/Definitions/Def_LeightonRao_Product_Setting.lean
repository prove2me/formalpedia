-- Prove2me | Definitions.Def_LeightonRao_Product_Setting
-- name    : LeightonRao_Product_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:05.006848+00:00
-- url     : https://prove2.me/theorems/8917141b-ca0d-4970-bcb1-5a6a4939272f
-- title:
--   §1.2, §2.2, §2.3, pp. 788–802 — capacitated network, cuts, concurrent max-flow, distance functions, PMFP node weights, product demands, weighted min-cut
-- statement:
--   This file fixes the objects of Leighton and Rao's treatment of **product multicommodity flow problems** (PMFPs).
--
--   **Network.** A network on a finite vertex set $V$ assigns to each unordered pair $\{u,v\}$ a capacity $C(u,v)\ge 0$, symmetric in $u,v$ and zero on the diagonal. The pair $\{u,v\}$ is an edge of the graph $G$ exactly when $C(u,v)>0$. For $U\subseteq V$ the cut capacity is
--   $$C(U,\bar U)=\sum_{u\in U}\sum_{v\notin U}C(u,v).$$
--   The network is *connected* if $C(U,\bar U)>0$ for every nonempty proper $U$ (the paper's standing assumption, p. 789).
--
--   **Concurrent flow.** Given demands $D(s,t)$ on ordered pairs $s\ne t$, a concurrent flow of value $\lambda$ routes, for every ordered pair $(s,t)$, a nonnegative arc flow $f_{st}(i\to j)$ that leaves $s$ with net amount $\lambda D(s,t)$, arrives at $t$, and is conserved elsewhere, such that on every edge $\{i,j\}$ the total flow of all commodities in both directions is at most $C(i,j)$. The **max-flow** $f$ is the supremum of the values $\lambda\ge0$ for which a concurrent flow exists.
--
--   **Distance functions.** A distance function assigns a length $d(u,v)\ge0$, symmetric in $u,v$; its *total weight* is $W=\sum_{e\in E}C(e)d(e)$. The distance $d(u,v)$ between nodes is the infimum of the lengths of walks in $G$ from $u$ to $v$, and $d(T,u)=\min_{t\in T}d(t,u)$. A vertex set $S$ has *radius at most $\Delta$* if some centre $c\in S$ reaches every $y\in S$ by a walk inside $S$ of length at most $\Delta$. For a partition of $V$, the *cross capacity* is the total capacity of the edges joining different parts.
--
--   **PMFP data (§2.3, p. 801).** A node weighting $\pi:V\to\mathbb R_{\ge0}$ has support $\mathcal P=\{u:\pi(u)\neq0\}$ of size $p=|\mathcal P|$, normalized (the paper's "without loss of generality") so that $\sum_{u\in V}\pi(u)=p$. Write $\pi(U)=\sum_{u\in U}\pi(u)$. The product demands give each ordered pair $u\ne v$ demand $\tfrac12\pi(u)\pi(v)$ (footnote 7), so the unordered pair has demand $\pi(u)\pi(v)$. The *weighted ratio cost* of a cut is $C(U,\bar U)/(\pi(U)\pi(\bar U))$, and the PMFP **min-cut** is
--   $$\mathcal S=\min_{U:\ \pi(U)>0,\ \pi(\bar U)>0}\frac{C(U,\bar U)}{\pi(U)\pi(\bar U)}.$$
--   The number of commodities with nonzero demand is $k=\binom p2$. A distance function satisfies the weighted distance constraint (p. 802) if
--   $$\sum_{\{u,v\}\in\mathcal P^2}\pi(u)\pi(v)\,d(u,v)\ge1 .$$
--
--   These are the objects of Theorem 7 and Lemmas 8–11 of the paper.
--
--   **Formalization Note** Commodities are indexed by ordered pairs with demand $\tfrac12\pi(u)\pi(v)$ each way (footnote 7). The min-cut ranges only over cuts with $\pi(U)>0$ and $\pi(\bar U)>0$: on the others the paper's ratio is undefined, and Lean's division by zero would return $0$. Max-flow is a real supremum; the set of feasible values contains $0$ and is bounded above whenever at least two nodes have positive weight. Graph distances are infima over walks and are $0$ for disconnected pairs, which is why every statement using them assumes connectivity. The weighted distance constraint is written as half the sum over ordered pairs. The radius is intrinsic: the walks stay inside the set.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 788–790 (§1.1–1.2), p. 796 (§2.2, Eq. (4), total weight W), pp. 801–802 (§2.3, footnote 7, PMFP min-cut and weighted distance constraint)

import Mathlib

namespace LeightonRao.Product

/-- An undirected capacitated network on the finite vertex type `V` (Leighton–Rao, §1.1–1.2,
pp. 788–789). `C u v ≥ 0` is the capacity of the undirected edge `{u, v}`; it is symmetric and
vanishes on the diagonal. The pair `{u, v}` is an edge iff `0 < C u v`. -/
structure Network (V : Type) where
  C : V → V → ℝ
  C_nonneg : ∀ u v, 0 ≤ C u v
  C_symm : ∀ u v, C u v = C v u
  C_self : ∀ u, C u u = 0

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The underlying simple graph: `u ~ v` iff the capacity of `{u, v}` is positive. -/
def Network.graph (N : Network V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => 0 < N.C u v)

/-- Cut capacity `C(U, Ū) = ∑_{u ∈ U} ∑_{v ∉ U} C(u, v)`; each undirected edge across the cut is
counted once. -/
def cutCap (N : Network V) (U : Finset V) : ℝ :=
  ∑ u ∈ U, ∑ v ∈ Uᶜ, N.C u v

/-- The standing assumption of p. 789: the network is connected, i.e. `C(U, Ū) > 0` for every
nonempty proper vertex set `U`. -/
def IsConnectedNet (N : Network V) : Prop :=
  ∀ U : Finset V, U.Nonempty → Uᶜ.Nonempty → 0 < cutCap N U

/-- A concurrent multicommodity flow of value `lam` for the demand matrix `D` (p. 789), in arc
form: one commodity per ordered pair `(s, t)` with `s ≠ t`; `f s t i j ≥ 0` is the amount of
commodity `(s, t)` on the arc `i → j`; commodity `(s, t)` has net outflow `lam * D s t` at `s`,
net inflow `lam * D s t` at `t` and is conserved elsewhere; the diagonal commodities carry
nothing; and on every undirected edge `{i, j}` the total flow in both directions is at most
`C i j`. -/
def IsConcurrentFlow (N : Network V) (D : V → V → ℝ) (f : V → V → V → V → ℝ) (lam : ℝ) :
    Prop :=
  (∀ s t i j, 0 ≤ f s t i j) ∧
  (∀ s t, s ≠ t → ∀ v, ∑ j, f s t v j - ∑ j, f s t j v =
      lam * D s t * ((if v = s then 1 else 0) - (if v = t then 1 else 0))) ∧
  (∀ s, ∀ i j, f s s i j = 0) ∧
  (∀ i j, ∑ s, ∑ t, (f s t i j + f s t j i) ≤ N.C i j)

/-- The (concurrent) max-flow `f` (p. 789): the supremum of the values `lam ≥ 0` for which a
concurrent flow of value `lam` exists. The set contains `0`; it is bounded above as soon as some
commodity of positive demand is separated by a cut (weak duality), which holds for the product
demands of a PMFP with at least two nodes of positive weight. -/
noncomputable def maxFlow (N : Network V) (D : V → V → ℝ) : ℝ :=
  sSup {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N D f lam}

/-- A distance function (p. 796): a nonnegative symmetric length `d u v`; only its values on
edges of the network matter. -/
def IsDistanceFunction (d : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ d u v) ∧ ∀ u v, d u v = d v u

/-- The total weight `W = ∑_{e ∈ E} C(e) d(e)` of a distance function (p. 796), each undirected
edge counted once. -/
noncomputable def totalWeight (N : Network V) (d : V → V → ℝ) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, N.C u v * d u v

/-- The length of a walk in the network graph with respect to the distance function `d`. -/
def walkLen (N : Network V) (d : V → V → ℝ) {u v : V} (p : N.graph.Walk u v) : ℝ :=
  (p.darts.map (fun a => d a.fst a.snd)).sum

/-- The shortest-path distance `d(u, v)` in `G` with respect to `d` (p. 796): the infimum of the
lengths of the walks from `u` to `v`. Meaningful when `u` and `v` are connected (the standing
connectivity assumption); it is `0` otherwise. -/
noncomputable def dist (N : Network V) (d : V → V → ℝ) (u v : V) : ℝ :=
  ⨅ p : N.graph.Walk u v, walkLen N d p

/-- The distance `d(T, u) = min_{t ∈ T} d(t, u)` from a vertex set `T` to `u` (it is `0` when
`T = ∅`). -/
noncomputable def distFrom (N : Network V) (d : V → V → ℝ) (T : Finset V) (u : V) : ℝ :=
  ⨅ t : T, dist N d t u

/-- `S` has radius at most `Δ` (Lemma 8 (1)): some centre `c ∈ S` reaches every `y ∈ S` by a walk
that stays inside `S` and has length at most `Δ`. -/
def HasRadiusLE (N : Network V) (d : V → V → ℝ) (S : Finset V) (Δ : ℝ) : Prop :=
  ∃ c ∈ S, ∀ y ∈ S, ∃ p : N.graph.Walk c y, (∀ x ∈ p.support, x ∈ S) ∧ walkLen N d p ≤ Δ

/-- The capacity of the edges linking nodes in different parts of the partition `P`, each
undirected edge counted once. -/
noncomputable def crossCap (N : Network V) (P : Finpartition (Finset.univ : Finset V)) : ℝ :=
  (1 / 2) * ∑ u, ∑ v, if P.part u = P.part v then 0 else N.C u v

/-- The node weight of a set: `π(U) = ∑_{u ∈ U} π(u)` (p. 801). -/
def piSum (π : V → ℝ) (U : Finset V) : ℝ :=
  ∑ u ∈ U, π u

/-- The set `𝒫` of nodes with nonzero weight (p. 801); `p = |𝒫|`. -/
noncomputable def support (π : V → ℝ) : Finset V :=
  Finset.univ.filter (fun u => π u ≠ 0)

/-- A PMFP node weighting (p. 801): `π(u) ≥ 0` for every node, normalized (the paper's "without
loss of generality") so that `∑_{u ∈ V} π(u) = p = |𝒫|`. -/
def IsPMFPWeight (π : V → ℝ) : Prop :=
  (∀ u, 0 ≤ π u) ∧ ∑ u, π u = ((support π).card : ℝ)

/-- The product demands (p. 801, footnote 7): for each ordered pair `u ≠ v`, a commodity from `u`
to `v` with demand `π(u)π(v)/2`, so the pair `{u, v}` has total demand `π(u)π(v)`. -/
noncomputable def productDemand (π : V → ℝ) : V → V → ℝ :=
  fun s t => if s = t then 0 else π s * π t / 2

/-- The weighted ratio cost `C(U, Ū) / (π(U) π(Ū))` of the cut `⟨U, Ū⟩` (p. 801). -/
noncomputable def weightedRatio (N : Network V) (π : V → ℝ) (U : Finset V) : ℝ :=
  cutCap N U / (piSum π U * piSum π Uᶜ)

/-- The min-cut `𝒮 = min_U C(U, Ū)/(π(U)π(Ū))` of a PMFP (p. 801), the minimum taken over the cuts
with `π(U) > 0` and `π(Ū) > 0` (on the other cuts the page's ratio is undefined). The index type is
nonempty when at least two nodes have positive weight. -/
noncomputable def pmfpMinCut (N : Network V) (π : V → ℝ) : ℝ :=
  ⨅ U : {U : Finset V // 0 < piSum π U ∧ 0 < piSum π Uᶜ}, weightedRatio N π U.1

/-- The number `k = (p choose 2)` of commodities with nonzero demand (p. 801), counted as
unordered pairs of nodes of `𝒫`. -/
noncomputable def numCommodities (π : V → ℝ) : ℕ :=
  Nat.choose (support π).card 2

/-- The weighted distance constraint of the PMFP dual (p. 802):
`∑_{{u,v} ∈ 𝒫²} π(u)π(v) d(u, v) ≥ 1`, written as half the sum over ordered pairs (the diagonal
terms vanish since `d(u, u) = 0`, and terms off `𝒫` vanish since `π = 0` there). -/
noncomputable def SatisfiesPMFPConstraint (N : Network V) (π : V → ℝ) (d : V → V → ℝ) : Prop :=
  1 ≤ (1 / 2) * ∑ u, ∑ v, π u * π v * dist N d u v

end LeightonRao.Product


