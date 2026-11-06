-- Prove2me | Definitions.Def_PottsRapidMixing_Cycles
-- name    : PottsRapidMixing_Cycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:24.115384+00:00
-- url     : https://prove2.me/theorems/8a70f8dd-7854-4a35-a221-cd2b581ecd87
-- title:
--   Cycle counts, the sum $T(G)$ and $W_{\mathrm{long}}$
-- statement:
--   For a graph $G$ on $V$: $|E(G[U])|$ is the number of edges with both endpoints in $U$; $N_j(G)$ is the number of cycles of length $j$; and
--   $$T(G)=\sum_{j=\ell+1}^{\mathrm{top}}j^2N_j(G)\,s^{\gamma(j-1)}.$$
--   For an edge set $A$, with $\mathcal C(A)$ the components of $(V,A)$,
--   $$W_{\mathrm{long}}(A)=\sum_{U\in\mathcal C(A)}|U|\,\mathbf 1\{G[U]\text{ contains a cycle longer than }\ell\}.$$
--
--   These objects express the treelike geometry of a random regular graph and the long-cycle error of the random-cluster dichotomy.
--
--   **Formalization Note** A cycle is counted once, by its edge set, and two cycles are different when their edge sets differ. $W_{\mathrm{long}}$ inspects the induced graph $G[U]$, not the open edges. A verification file evaluates $W_L$ and $W_{\mathrm{long}}$ on the triangle.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, (2.13), p.13; Lemma 3.12 and (3.27), p.23

import Mathlib
import Definitions.Def_PottsRapidMixing_ChainM

open scoped Classical

namespace PottsRapidMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `|E(G[U])|`, the number of edges of `G` with both endpoints in `U` (Blanca, Gheissari, Park,
Zhang, arXiv:2610.42059, pp.21, 23). -/
noncomputable def edgesIn (G : SimpleGraph V) (U : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∀ a ∈ e, a ∈ U)).card

/-- `N_j(G)`, the number of cycles of length `j` in `G`, (3.27) (arXiv:2610.42059, p.23).

**Formalization Note.** A cycle is counted once, as an unoriented subgraph: the objects counted are
the edge sets of cyclic walks. -/
noncomputable def cycleCount (G : SimpleGraph V) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun S : Finset (Sym2 V) =>
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = j ∧ c.edges.toFinset = S)).card

/-- "All simple cycles of length at most `ℓ` are pairwise vertex-disjoint" (arXiv:2610.42059,
pp.13, 23). Two cycles are the same when they have the same edge set. -/
def ShortCyclesDisjoint (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∀ (u v : V) (c : G.Walk u u) (c' : G.Walk v v), c.IsCycle → c'.IsCycle →
    c.length ≤ ℓ → c'.length ≤ ℓ → c.edges.toFinset ≠ c'.edges.toFinset →
    Disjoint c.support.toFinset c'.support.toFinset

/-- `T(G) = ∑_{j=ℓ+1}^{top} j² N_j(G) s^{γ(j−1)}`, (3.27) (arXiv:2610.42059, p.23). The power is a
real power with exponent `γ(j − 1)`. -/
noncomputable def cycleSum (G : SimpleGraph V) (s γ : ℝ) (ℓ top : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc ℓ top, (j : ℝ) ^ 2 * (cycleCount G j : ℝ) * s ^ (γ * ((j : ℝ) - 1))

/-- `G[U]` contains a cycle longer than `ℓ` (arXiv:2610.42059, p.13). This looks at the graph induced
by `G` on `U`, not at the open edges. -/
def HasLongCycle (G : SimpleGraph V) (ℓ : ℕ) (U : Finset V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ℓ < c.length ∧ ∀ w ∈ c.support, w ∈ U

/-- `W_long(A) = ∑_{U ∈ C(A)} |U| 1{G[U] contains a cycle longer than ℓ}`, (2.13)
(arXiv:2610.42059, p.13). -/
noncomputable def Wlong (G : SimpleGraph V) (ℓ : ℕ) (A : G.edgeSet → Bool) : ℝ :=
  ∑ U ∈ compSets (edgeGraph G A), if HasLongCycle G ℓ U then (U.card : ℝ) else 0

end PottsRapidMixing


