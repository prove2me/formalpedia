-- Prove2me | Definitions.Def_PPRInstOpt_UnknownN_Graph
-- name    : PPRInstOpt_UnknownN_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:11:05.021751+00:00
-- url     : https://prove2.me/theorems/cd58a148-46d1-4483-9c72-cf5d2d6a78c6
-- title:
--   Digraphs with adjacency lists, the oracle, personalized PageRank π(u, v), π(u, E̅′, v), T_f, T_b and T*
-- statement:
--   A **valid graph** is a finite directed graph $G=(V,E)$ given by adjacency lists: for each vertex $v$ an ordered list $N_{\mathrm{out}}(v)$ of out-neighbours and an ordered list $N_{\mathrm{in}}(v)$ of in-neighbours, with no repeated entries, no self-loops, the two families describing the same edge set, and every out-degree $d_{\mathrm{out}}(v)\ge 1$. The vertex type is arbitrary, so labels carry no information about $n=|V|$. The **oracle** of $G$ answers $\mathrm{outdeg}(v)$, $\mathrm{indeg}(v)$, $\mathrm{out}(v,i)$, $\mathrm{in}(v,i)$ (entry $i$ of the list, counted from $0$, or nothing past the end).
--
--   With $P(u,w)=1/d_{\mathrm{out}}(u)$ for $(u,w)\in E$ and $0$ otherwise, the **personalized PageRank** of $v$ with respect to $u$ is the probability that an $\alpha$-discounted random walk from $u$ (stop with probability $\alpha$, otherwise move to a uniform out-neighbour) terminates at $v$:
--   $$\pi(u,v)=\sum_{k\ge 0}\alpha(1-\alpha)^k\,(P^k)(u,v).$$
--   For a set $E'$ of edges, $\pi(u,\overline{E'},v)$ is the same series with the edges of $E'$ deleted from $P$: the probability that the walk terminates at $v$ without traversing an edge of $E'$.
--
--   For $s,t$ with $\pi(s,t)>0$ (Eq. (17)):
--   $T_f(r)=\sum_{u:\pi(s,u)>0}\min\{d_{\mathrm{out}}(u),\,\pi(s,u)r/\pi(s,t)\}$, $T_b(r)=\sum_{v:\pi(v,t)\ge r}(1+d_{\mathrm{in}}(v))$, and $T^*=\sup_{r\in(0,1]}\min\{T_f(r),T_b(r)\}$ (the family is bounded by $\sum_u d_{\mathrm{out}}(u)$; the paper writes $\max$).
--
--   Finally `subdivOut G u v` is the out-list family on $V\cup\{w\}$ (with $w$ a new vertex, `none` on `Option V`) obtained by replacing the edge $(u,v)$ by $(u,w),(w,v)$, the edge $(u,w)$ taking the place of $(u,v)$ in $u$'s list (Lemma 5.3).
--
--   **Formalization Note** Adjacency-list indices start at $0$ (the paper's $\mathrm{out}(v,i)$ is the $i$-th neighbour). $T^*$ is a real `⨆` over the nonempty bounded index set $(0,1]$.
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 1, 3, 5, 23, 32-33, Abstract, §1.2, §1.4, Eq. (17), §5 notation, Lemma 5.3

import Mathlib

open scoped BigOperators

namespace PPRInstOpt.UnknownN

/-- A finite simple directed graph given by its adjacency lists (§1.4, p. 5).
`outList v` is the out-neighbour list of `v` in its fixed order (so `out(v, i)` is its entry `i`,
counted from `0`), `inList v` the in-neighbour list. No parallel edges (`Nodup`), no self-loops,
the two lists describe the same edge set, and every out-degree is at least one (p. 1, p. 24).
The vertex type is arbitrary: labels are opaque and reveal nothing about `n`. -/
structure Digraph (V : Type) where
  outList : V → List V
  inList : V → List V
  outList_nodup : ∀ v, (outList v).Nodup
  inList_nodup : ∀ v, (inList v).Nodup
  not_mem_outList_self : ∀ v, v ∉ outList v
  mem_inList_iff : ∀ u v, u ∈ inList v ↔ v ∈ outList u
  outList_ne_nil : ∀ v, outList v ≠ []

namespace Digraph

variable {V : Type}

/-- `dout(v)`. -/
def dout (G : Digraph V) (v : V) : ℕ := (G.outList v).length

/-- `din(v)`. -/
def din (G : Digraph V) (v : V) : ℕ := (G.inList v).length

end Digraph

/-- The adjacency-list query interface (§1.4, p. 5): `outdeg v`, `indeg v`, `out(v, i)`,
`in(v, i)` (indices from `0`; an index past the end answers `none`). An algorithm sees the graph
only through this record and the vertices it is handed (`s`, `t`) or that the oracle returns. -/
structure Oracle (V : Type) where
  outdeg : V → ℕ
  indeg : V → ℕ
  outNbr : V → ℕ → Option V
  inNbr : V → ℕ → Option V

/-- The oracle of a digraph. -/
def Digraph.oracle {V : Type} (G : Digraph V) : Oracle V where
  outdeg v := G.dout v
  indeg v := G.din v
  outNbr v i := (G.outList v)[i]?
  inNbr v i := (G.inList v)[i]?

/-- The out-neighbour list of `u` read through the oracle (`outdeg u` and `out(u, i)` queries). -/
def Oracle.outs {V : Type} (o : Oracle V) (u : V) : List V :=
  (List.range (o.outdeg u)).filterMap (o.outNbr u)

/-- The in-neighbour list of `v` read through the oracle (`indeg v` and `in(v, i)` queries). -/
def Oracle.ins {V : Type} (o : Oracle V) (v : V) : List V :=
  (List.range (o.indeg v)).filterMap (o.inNbr v)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The random-walk transition matrix `P(u, w) = 1/dout(u)` for `(u, w) ∈ E`, else `0`. -/
noncomputable def transMat (G : Digraph V) : Matrix V V ℝ :=
  fun u w => if w ∈ G.outList u then 1 / (G.dout u : ℝ) else 0

/-- The transition matrix with the edges of `E'` removed: `P_{E'}(u, w) = P(u, w)` if
`(u, w) ∉ E'`, else `0`. Its `k`-th power at `(u, v)` is the probability that the
(non-terminating) walk from `u` is at `v` after `k` steps without having traversed an edge of
`E'`. -/
noncomputable def transMatAvoid (G : Digraph V) (E' : Finset (V × V)) : Matrix V V ℝ :=
  fun u w => if w ∈ G.outList u ∧ (u, w) ∉ E' then 1 / (G.dout u : ℝ) else 0

/-- Personalized PageRank `π(u, v)` (p. 1, p. 3): the probability that an `α`-discounted random
walk from `u` (stop with probability `α`, else move to a uniform out-neighbour) terminates at
`v`, i.e. `π(u, v) = Σ_{k ≥ 0} α (1 - α)^k P^k(u, v)`. -/
noncomputable def ppr (α : ℝ) (G : Digraph V) (u v : V) : ℝ :=
  ∑' k : ℕ, α * (1 - α) ^ k * ((transMat G) ^ k) u v

/-- `π(u, \overline{E'}, v)` (§5, p. 32): the probability that the `α`-discounted walk from `u`
terminates at `v` without traversing any edge of `E'`. -/
noncomputable def pprAvoid (α : ℝ) (G : Digraph V) (E' : Finset (V × V)) (u v : V) : ℝ :=
  ∑' k : ℕ, α * (1 - α) ^ k * ((transMatAvoid G E') ^ k) u v

open scoped Classical in
/-- `T_f(r) = Σ_{u : π(s,u) > 0} min{dout(u), π(s,u) r / π(s,t)}` (Eq. (17), p. 23). -/
noncomputable def Tf (α : ℝ) (G : Digraph V) (s t : V) (r : ℝ) : ℝ :=
  ∑ u ∈ Finset.univ.filter (fun u => 0 < ppr α G s u),
    min (G.dout u : ℝ) (ppr α G s u * r / ppr α G s t)

open scoped Classical in
/-- `T_b(r) = Σ_{v : π(v,t) ≥ r} (1 + din(v))` (Eq. (17), p. 23). -/
noncomputable def Tb (α : ℝ) (G : Digraph V) (t : V) (r : ℝ) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => r ≤ ppr α G v t), (1 + (G.din v : ℝ))

/-- `T* = max_{r ∈ (0,1]} min{T_f(r), T_b(r)}` (Eq. (17), p. 23), written as a supremum over the
nonempty index set `(0, 1]`; the family is bounded above by `Σ_u dout(u)`, so this is the true
supremum (and the paper's maximum when it is attained). Meaningful when `π(s, t) > 0`. -/
noncomputable def Tstar (α : ℝ) (G : Digraph V) (s t : V) : ℝ :=
  ⨆ r : Set.Ioc (0 : ℝ) 1, min (Tf α G s t r) (Tb α G t r)

/-- The out-lists after subdividing the edge `(u, v)` (Lemma 5.3, p. 33): the vertex set becomes
`Option V`, the new vertex is `none`, `(u, none)` takes the place of `(u, v)` in `u`'s list, and
the only out-edge of `none` is `(none, v)`. -/
def subdivOut (G : Digraph V) (u v : V) : Option V → List (Option V)
  | none => [some v]
  | some x => (G.outList x).map (fun y => if x = u ∧ y = v then none else some y)

end PPRInstOpt.UnknownN


