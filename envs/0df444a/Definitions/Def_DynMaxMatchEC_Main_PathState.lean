-- Prove2me | Definitions.Def_DynMaxMatchEC_Main_PathState
-- name    : DynMaxMatchEC_Main_PathState
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:02:29.27532+00:00
-- url     : https://prove2.me/theorems/ee7736aa-a900-45e3-9e9b-ad505edf9229
-- title:
--   The matching algorithm's state, the alternating paths P_i(v) (long, bad, terrible), the sets J(u), and the failure probabilities of ProcSettleS and ProcAugment
-- statement:
--   An **abstract state** (`MState n z'`) of the matching algorithm of §3.2 consists of: a graph $G$ on $n$ vertices; a set $S$ (with $U=V\setminus S$); the low-degree set $A$ (with $\bar A=U\setminus A$); transit sets $T$ and $\hat T$; matchings $M_1,\dots,M_{z'}$ (the color classes of $M$; indexed $0,\dots,z'-1$); the matching $M^*$; index sets $I(u)$; vertex sets $\hat\Lambda(v)$ and the first $r$ entries of $\hat\Lambda(v)$ kept by the extended search structure. No invariant is built in. We write $m(v)$ for the number of edges of $M=\bigcup_iM_i$ at $v$, $S'=\{v\in S$ unmatched in $M^*\}$ and $\bar A'=\{v\in\bar A$ unmatched in $M^*\}$.
--
--   **Paths.** For an index $i$ and a vertex $v$ unmatched in $M_i$ or in $M^*$, $P_i(v)$ is the component of the multigraph $M^*\cup M_i$ that is a path ending at $v$: starting at $v$, follow alternately the partner in the matching in which the current vertex is matched (first $M^*$ if $v$ is unmatched in $M_i$, otherwise $M_i$), until no partner exists. Its last vertex is $\gamma_i(v)$. $P_i(v)$ is **long** if it has at least $z$ edges, **terrible** if $\gamma_i(v)\in S$ and $\gamma_i(v)$ is unmatched in $M_i$, and **bad** if $\gamma_i(v)\in\bar A$ and $\gamma_i(v)$ is unmatched in $M_i$. $J(u)$ is the set of indices $i$ for which $P_i(u)$ is defined, short, not terrible and has at least one edge.
--
--   **ProcSettleS (Figure 5).** For $v\in S'$ and $r=\lceil64\rho xn/\hat x\rceil$, its failure probability is $0$ if some neighbour of $v$ in $S'\cup\bar A'\cup T\cup\hat T$ is unmatched in $M^*$ (Step 2) or $|\hat\Lambda(v)|\le r$ (Step 3). Otherwise it is
--   $$\frac1{r}\sum_{u}\;q(u),$$
--   summing over the first $r$ entries $u$ of $\hat\Lambda(v)$ (Step 4, uniform choice), where $q(u)=0$ if $u$ is unmatched in $M^*$ (Step 5), and otherwise $q(u)$ is the fraction of $i\in I(u)$ (Step 6, uniform choice) for which $P_i(u)$ is long or terrible (Step 7, FAIL); $q(u)=1$ if $I(u)$ is empty.
--
--   **ProcAugment (Figure 6).** For an index $i^*$ and threshold $\theta$, its failure probability is $0$ if $|S'\cup\bar A'|\le\theta$ (Step 1), and otherwise the fraction of $v\in S'\cup\bar A'$ (Step 3, uniform choice) for which $P_{i^*}(v)$ is long, has no edge, is terrible or is bad (Step 4, FAIL).
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), pp. 25–32, §3.2 (Long, Bad and Terrible Paths, p. 30; the sets J(v), p. 31); pp. 34–39, Figures 5 and 6

import Mathlib
import Definitions.Def_DynMaxMatchEC_Main_Model

namespace DynMaxMatchEC.Main

/-!
# The matching algorithm's state, the alternating paths `P_i(v)`, and the two random procedures

Chuzhoy, *New Algorithms for Dynamic Maximal Matching and Edge Coloring* (manuscript, Nov. 1,
2026; PDF sha256 2c277528…4ca5), §3.2 pp. 25–32 (data structures, "Long, Bad and Terrible
Paths" p. 30, the sets `J(v)` p. 31), §3.3 pp. 34–39 (Figures 5 and 6).

* `MState n z'` is an abstract snapshot of the state used in §3.2–3.4: the graph `G` on `Fin n`; the
  set `S` (so `U = V \ S`); the low-degree set `A` (so `Ā = U \ A = V \ (S ∪ A)`); the transit sets
  `T` and `T̂`; the matchings `M_1, …, M_{z'}` of the `z'`-edge-coloring of `M` (indexed by
  `Fin z'`, i.e. `I` shifted to start at `0`); the matching `M∗`; the index sets `I(u)`; the sets
  `Λ̂(v)`; and the `r` vertices of `Λ̂(v)` that the extended search structure keeps as its first
  entries (`Λ̂first v`). No invariant is built in: each claim states the invariants it uses.
* `P_i(v)` is the path component of the multigraph `M∗ ∪ M_i` with endpoint `v`; it is defined iff
  `v` is unmatched in `M_i` or in `M∗`. It is followed from `v` by alternately taking the partner
  of the current vertex in the two matchings, starting with the matching in which `v` is matched
  (`M∗` when `v` is unmatched in `M_i`), until no partner exists. `pathVertex σ i v k` is its `k`-th
  vertex (`k = 0` is `v`), `none` beyond its last vertex.
* `P_i(v)` is **long** if it has at least `z` edges (its `z`-th vertex exists); `γ_i(v)` is its last
  vertex; it is **terrible** if `γ_i(v) ∈ S` and `γ_i(v)` is unmatched in `M_i`, and **bad** if
  `γ_i(v) ∈ Ā` and `γ_i(v)` is unmatched in `M_i`.
* `J(u)` is the set of indices `i` such that `P_i(u)` is defined, short, not terrible and has at
  least one edge (the semantic set of p. 31).
* The two random procedures are written as exact uniform-counting probabilities.
  `settleSFailProb` is the probability that `ProcSettleS(v)` (Figure 5) ends with FAIL: `0` if Step 2
  finds an unmatched neighbour of `v` in `W = S′ ∪ Ā′ ∪ T ∪ T̂` or if `|Λ̂(v)| ≤ r` (Step 3); otherwise
  `u` is uniform among the first `r` vertices of `Λ̂(v)` (Step 4), the procedure stops if `u` is
  unmatched in `M∗` (Step 5), and otherwise `i` is uniform in `I(u)` (Step 6) and it fails iff
  `P_i(u)` is long or terrible (Step 7); if `I(u)` were empty Step 6 could not run, and this is
  counted as failure. `augmentFailProb` is the probability that `ProcAugment` (Figure 6) ends with
  FAIL: `0` if `|S′| + |Ā′| ≤ thr` (Step 1); otherwise `v` is uniform in `S′ ∪ Ā′` (Step 3) and it
  fails iff `P_{i∗}(v)` is long, has no edge, is terrible or is bad (Step 4).
-/

/-- The partner of `v` in the edge set `M`: some `u` with `uv ∈ M`, if there is one (unique when `M`
is a matching). -/
noncomputable def partner {n : ℕ} (M : Finset (Sym2 (Fin n))) (v : Fin n) : Option (Fin n) :=
  open Classical in
  if h : ∃ u : Fin n, s(v, u) ∈ M then some h.choose else none

/-- The walk from `v` that alternately follows `A` and `B`, starting with `A`: its `k`-th vertex, or
`none` once a vertex has no partner in the matching to be followed. -/
noncomputable def altWalk {n : ℕ} (A B : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ → Option (Fin n)
  | 0 => some v
  | k + 1 => (altWalk A B v k).bind (partner (if k % 2 = 0 then A else B))

/-- An abstract state of the matching algorithm of §3.2 (`z'` matchings `M_i`). -/
structure MState (n z' : ℕ) where
  G : SimpleGraph (Fin n)
  S : Finset (Fin n)
  A : Finset (Fin n)
  T : Finset (Fin n)
  That : Finset (Fin n)
  col : Fin z' → Finset (Sym2 (Fin n))
  Mstar : Finset (Sym2 (Fin n))
  Iset : Fin n → Finset (Fin z')
  Lhat : Fin n → Finset (Fin n)
  Lfirst : Fin n → Finset (Fin n)

namespace MState

variable {n z' : ℕ} (σ : MState n z')

/-- `M = M_1 ∪ … ∪ M_{z'}`. -/
def Mall : Finset (Sym2 (Fin n)) :=
  Finset.univ.biUnion σ.col

/-- `Ā = U \ A = V \ (S ∪ A)`. -/
def Abar : Finset (Fin n) :=
  (Finset.univ \ σ.S) \ σ.A

open Classical in
/-- `S′`: the vertices of `S` unmatched in `M∗`. -/
noncomputable def S' : Finset (Fin n) :=
  σ.S.filter fun v => ¬ IsMatchedIn σ.Mstar v

open Classical in
/-- `Ā′`: the vertices of `Ā` unmatched in `M∗`. -/
noncomputable def Abar' : Finset (Fin n) :=
  σ.Abar.filter fun v => ¬ IsMatchedIn σ.Mstar v

/-- `P_i(v)` is defined: `v` is unmatched in `M_i` or in `M∗`. -/
def PathDefined (i : Fin z') (v : Fin n) : Prop :=
  ¬ IsMatchedIn (σ.col i) v ∨ ¬ IsMatchedIn σ.Mstar v

open Classical in
/-- The `k`-th vertex of `P_i(v)` (`k = 0` is `v`), `none` beyond its last vertex. -/
noncomputable def pathVertex (i : Fin z') (v : Fin n) : ℕ → Option (Fin n) :=
  if IsMatchedIn (σ.col i) v then altWalk (σ.col i) σ.Mstar v else altWalk σ.Mstar (σ.col i) v

/-- `P_i(v)` is long: it has at least `z` edges. -/
def IsLong (z : ℕ) (i : Fin z') (v : Fin n) : Prop :=
  (σ.pathVertex i v z).isSome

/-- `P_i(v)` has at least one edge. -/
def HasEdge (i : Fin z') (v : Fin n) : Prop :=
  (σ.pathVertex i v 1).isSome

open Classical in
/-- `γ_i(v)`, the last vertex of `P_i(v)` (the vertex after which the walk stops). -/
noncomputable def farEnd (i : Fin z') (v : Fin n) : Option (Fin n) :=
  if h : ∃ k : ℕ, σ.pathVertex i v (k + 1) = none then σ.pathVertex i v (Nat.find h) else none

/-- `P_i(v)` is terrible: `γ_i(v) ∈ S` and `γ_i(v)` is unmatched in `M_i`. -/
def IsTerrible (i : Fin z') (v : Fin n) : Prop :=
  ∃ γ, σ.farEnd i v = some γ ∧ γ ∈ σ.S ∧ ¬ IsMatchedIn (σ.col i) γ

/-- `P_i(v)` is bad: `γ_i(v) ∈ Ā` and `γ_i(v)` is unmatched in `M_i`. -/
def IsBad (i : Fin z') (v : Fin n) : Prop :=
  ∃ γ, σ.farEnd i v = some γ ∧ γ ∈ σ.Abar ∧ ¬ IsMatchedIn (σ.col i) γ

open Classical in
/-- `J(u)`: the indices `i` such that `P_i(u)` is defined, short (fewer than `z` edges), not
terrible, and has at least one edge. -/
noncomputable def J (z : ℕ) (u : Fin n) : Finset (Fin z') :=
  Finset.univ.filter fun i =>
    σ.PathDefined i u ∧ ¬ σ.IsLong z i u ∧ ¬ σ.IsTerrible i u ∧ σ.HasEdge i u

open Classical in
/-- The probability that `ProcSettleS(v)` (Figure 5) ends with FAIL, with long-path threshold `z`
and `r = ⌈64ρxn/x̂⌉`. -/
noncomputable def settleSFailProb (z r : ℕ) (v : Fin n) : ℝ :=
  if (∃ u ∈ σ.S' ∪ σ.Abar' ∪ σ.T ∪ σ.That, σ.G.Adj v u ∧ ¬ IsMatchedIn σ.Mstar u) ∨
      (σ.Lhat v).card ≤ r then 0
  else
    (1 / ((σ.Lfirst v).card : ℝ)) *
      ∑ u ∈ σ.Lfirst v,
        (if ¬ IsMatchedIn σ.Mstar u then (0 : ℝ)
         else if σ.Iset u = ∅ then 1
         else (((σ.Iset u).filter fun i => σ.IsLong z i u ∨ σ.IsTerrible i u).card : ℝ) /
           ((σ.Iset u).card : ℝ))

open Classical in
/-- The probability that `ProcAugment` (Figure 6) ends with FAIL, for the index `i∗`, the long-path
threshold `z` and the Step 1 threshold `thr = 32nx̂/z`. -/
noncomputable def augmentFailProb (z : ℕ) (istar : Fin z') (thr : ℝ) : ℝ :=
  if ((σ.S' ∪ σ.Abar').card : ℝ) ≤ thr then 0
  else
    (((σ.S' ∪ σ.Abar').filter fun v =>
        σ.IsLong z istar v ∨ ¬ σ.HasEdge istar v ∨ σ.IsTerrible istar v ∨ σ.IsBad istar v).card : ℝ) /
      ((σ.S' ∪ σ.Abar').card : ℝ)

end MState

end DynMaxMatchEC.Main


