-- Prove2me | Definitions.Def_ZeroExtensionGap_MGraph
-- name    : ZeroExtensionGap_MGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:03.565098+00:00
-- url     : https://prove2.me/theorems/e00a039f-fa46-4b83-895f-1ad40837cac9
-- title:
--   Multigraphs: walks, distance, edge counts, fractional arboricity and forests
-- statement:
--   §2 calls a graph simple when it has neither self-loops nor parallel edges, so the graphs of Theorem 3 and Lemmas 13 and 15 may have parallel edges. A finite multigraph is given by $\mathrm{ends}:E\to\mathrm{Sym}^2V$. Its shortest-path distance is the infimum of total length over walks, $\infty$ when no walk exists. $|E(G[S])|$ counts the edges with both ends in $S$, with multiplicity. $\Gamma(G)$ is given by the formula of §2. A set of edges is a **forest** if it has no self-loop, no two parallel edges (two parallel edges form a cycle) and its underlying simple graph is acyclic.
--
--   **Formalization Note.** `MConnected ends x y` is the guard under which the real value of `mdist` is the distance. The published definition `PoSUndirected_IsSimplePathEdges` (9b5db71f) has the same conventions, but a direct read showed `visibility: private`, so it is not referenced; see `MODERATION_NOTES.md`.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), §2, p.5 (PDF p.7); Theorem 3, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_ZeroExtensionGap_fractionalArboricity

open scoped ENNReal

namespace ZeroExtensionGap

variable {V E : Type*}

/-- A walk in a multigraph given by the endpoint map `ends : E → Sym2 V`: `IsMWalk ends x l y` says
the edge list `l` is a walk from `x` to `y`. §2 of Chen, Zhu, *Almost Tight Hardness of Approximation
for 0-Extension*, STOC 2027 submission (manuscript sha256 0cdea87b…), p.5 (PDF p.7): a graph is
*simple* when it has neither self-loops nor parallel edges, so a "graph" may have both. -/
inductive IsMWalk (ends : E → Sym2 V) : V → List E → V → Prop
  | nil (x : V) : IsMWalk ends x [] x
  | cons {x y z : V} {e : E} {l : List E} :
      ends e = s(x, y) → IsMWalk ends y l z → IsMWalk ends x (e :: l) z

/-- The shortest-path distance of a multigraph with edge lengths `ℓ`, `∞` if no path exists (§2,
p.5, PDF p.7): the infimum over walks. -/
noncomputable def mdist (ends : E → Sym2 V) (ℓ : E → ℝ) (x y : V) : ℝ≥0∞ :=
  ⨅ (l : List E) (_ : IsMWalk ends x l y), ENNReal.ofReal (l.map ℓ).sum

/-- `x` and `y` are connected in the multigraph. -/
def MConnected (ends : E → Sym2 V) (x y : V) : Prop := ∃ l, IsMWalk ends x l y

open Classical in
/-- `|E(G[S])|` for a multigraph: the edges with both ends in `S`, counted with multiplicity. -/
noncomputable def mEdgeCount [Fintype E] (ends : E → Sym2 V) (S : Finset V) : ℕ :=
  (Finset.univ.filter fun e => ∀ v ∈ ends e, v ∈ S).card

/-- The fractional arboricity `Γ(G)` of a multigraph (§2, p.5, PDF p.7). -/
noncomputable def mFracArb [Fintype V] [Fintype E] (ends : E → Sym2 V) : ℝ :=
  fracArbOf (mEdgeCount ends)

/-- The edge set `s` is a forest of the multigraph: no self-loop, no two parallel edges ("two parallel
edges form a cycle", p.22, PDF p.24), and the underlying simple graph is acyclic. -/
def MIsForest (ends : E → Sym2 V) (s : Set E) : Prop :=
  (∀ e ∈ s, ¬ (ends e).IsDiag) ∧ Set.InjOn ends s ∧
    (SimpleGraph.fromEdgeSet (ends '' s)).IsAcyclic

end ZeroExtensionGap


