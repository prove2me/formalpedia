-- Prove2me | Definitions.Def_BipDijoin_IsStrongEnd
-- name    : BipDijoin_IsStrongEnd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:47:06.756582+00:00
-- url     : https://prove2.me/theorems/af463999-5b2c-4959-8452-baa4c60cf533
-- title:
--   The alternating digraph $G_M$, source and sink SCCs, strong ends, fitting and volume
-- statement:
--   Let $M$ be a matching of a bipartite multigraph $G$. The **alternating digraph** $G_M$ has an arc $\ell(e)\to r(e)$ for every edge $e$ (matched or not) and, in addition, the reverse arc $r(e)\to\ell(e)$ for every $e\in M$.
--
--   For a digraph and a vertex set $S$, a **strongly connected component** (SCC) of the subdigraph induced by $S$ is a nonempty maximal set $U\subseteq S$ of mutually reachable vertices (paths inside $S$, the trivial path included). It is a **source** SCC if no arc enters $U$ from $S\setminus U$, a **sink** SCC if no arc leaves $U$ into $S\setminus U$, and **nontrivial** if $|U|\ge 2$.
--
--   **Definition 2.1.** A set $U\subseteq V(G)$ is a **source strong end** (resp. **sink strong end**) if it is a nontrivial source (resp. sink) SCC of $G_M$ for some matching $M$ of $G$. A matching $M$ **fits** $U$ if its restriction to $U$ is a perfect matching of $G[U]$.
--
--   The **volume** $\mathrm{vol}_{G_M}(U)$ is the sum over $v\in U$ of the out-degree of $v$ in $G_M$: the number of edges with left end $v$ plus the number of edges of $M$ with right end $v$ (§5.2).
--
--   **Formalization Note** The paper notes that fitting is equivalent to $U$ being a source or sink SCC of $G_M$; here fitting is defined directly by its first description.
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), §2.2, Definition 2.1, p.3 (PDF p.5); §5.2, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching

set_option autoImplicit false

namespace BipDijoin

/-!
# The alternating digraph, its strongly connected components, and strong ends

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), §2.2, p.3 (PDF p.5):
"For a matching M of G, the alternating digraph G_M contains every edge directed from L to R and
the reverse arc of every edge in M. A strongly connected component (SCC) is nontrivial if it
contains at least two vertices.
Definition 2.1 (Bipartite strong end). A set U ⊆ V(G) is a source strong end (respectively, sink
strong end) if it is a nontrivial source (respectively, sink) SCC of G_M for some matching M of G.
A source strong end satisfies N_G(U_R) = U_L; a sink strong end satisfies N_G(U_L) = U_R.
A matching M fits a strong end U if its restriction to U is a perfect matching of G[U];
equivalently, U is a source or sink SCC of G_M."
§5.2, p.18 (PDF p.20): "deg(v) denotes the outdegree of v in G_M, and the volume of a set is the
sum of these outdegrees."

**Formalization Note.**
* `altArc G M u v`: some edge is the arc `u → v` (`tl e = u`, `hd e = v`; matched or not), or
  some edge of `M` is the reverse arc `u → v` (`hd e = u`, `tl e = v`).
* SCCs are taken inside a vertex set `S` (the subdigraph induced by `S`): `ReachIn arc S u v` is
  reachability by arcs with both ends in `S` (the trivial path included). An SCC of `D[S]` is a
  nonempty, mutually reachable, maximal `U ⊆ S`. A **source** SCC has no arc from `S ∖ U` into
  `U`; a **sink** SCC has no arc from `U` to `S ∖ U`. Nontrivial means `2 ≤ |U|`.
* The volume counts out-arcs in all of `G_M` (parallel arcs counted with multiplicity): edges
  with tail `v`, plus edges of `M` with head `v`.
-/

/-- Reachability inside `S`: the reflexive-transitive closure of the arcs with both ends in `S`. -/
def ReachIn (arc : ℕ → ℕ → Prop) (S : Finset ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ arc a b)

/-- `U` is a strongly connected component of the digraph `arc` restricted to `S`. -/
def IsSCCIn (arc : ℕ → ℕ → Prop) (S U : Finset ℕ) : Prop :=
  U ⊆ S ∧ U.Nonempty ∧ (∀ u ∈ U, ∀ v ∈ U, ReachIn arc S u v) ∧
    ∀ v ∈ S, ∀ u ∈ U, ReachIn arc S u v → ReachIn arc S v u → v ∈ U

/-- A **source SCC** of `arc` restricted to `S`: an SCC with no arc entering it from `S`. -/
def IsSourceSCC (arc : ℕ → ℕ → Prop) (S U : Finset ℕ) : Prop :=
  IsSCCIn arc S U ∧ ∀ u ∈ S, ∀ v ∈ U, arc u v → u ∈ U

/-- A **sink SCC** of `arc` restricted to `S`: an SCC with no arc leaving it inside `S`. -/
def IsSinkSCC (arc : ℕ → ℕ → Prop) (S U : Finset ℕ) : Prop :=
  IsSCCIn arc S U ∧ ∀ u ∈ U, ∀ v ∈ S, arc u v → v ∈ U

namespace BipGraph

variable (G : BipGraph)

/-- The arcs of the **alternating digraph** `G_M`: every edge from `L` to `R`, and the reverse of
every edge of `M` (§2.2, p.3). -/
def altArc (M : Finset ℕ) (u v : ℕ) : Prop :=
  (∃ e ∈ G.E, G.tl e = u ∧ G.hd e = v) ∨ (∃ e ∈ M, G.hd e = u ∧ G.tl e = v)

/-- A **source strong end** (Definition 2.1): a nontrivial source SCC of `G_M` for some matching
`M` of `G`. -/
def IsSourceEnd (U : Finset ℕ) : Prop :=
  2 ≤ U.card ∧ ∃ M, G.IsMatching M ∧ IsSourceSCC (G.altArc M) G.V U

/-- A **sink strong end** (Definition 2.1): a nontrivial sink SCC of `G_M` for some matching
`M` of `G`. -/
def IsSinkEnd (U : Finset ℕ) : Prop :=
  2 ≤ U.card ∧ ∃ M, G.IsMatching M ∧ IsSinkSCC (G.altArc M) G.V U

/-- A (nontrivial) **strong end**: a source or a sink strong end. -/
def IsStrongEnd (U : Finset ℕ) : Prop := G.IsSourceEnd U ∨ G.IsSinkEnd U

/-- `M` **fits** `U`: its restriction to `U` is a perfect matching of `G[U]` (Definition 2.1). -/
def Fits (M U : Finset ℕ) : Prop :=
  ∀ v ∈ U, ∃ e ∈ M, G.tl e ∈ U ∧ G.hd e ∈ U ∧ (G.tl e = v ∨ G.hd e = v)

/-- The out-degree of `v` in `G_M`: edges with tail `v` plus matching edges with head `v`. -/
def outdeg (M : Finset ℕ) (v : ℕ) : ℕ :=
  (G.E.filter (fun e => G.tl e = v)).card + (M.filter (fun e => G.hd e = v)).card

/-- The volume `vol_{G_M}(U)`: the sum of the out-degrees in `G_M` of the vertices of `U`
(§5.2, p.18). -/
def vol (M U : Finset ℕ) : ℕ := ∑ v ∈ U, G.outdeg M v

end BipGraph

end BipDijoin


