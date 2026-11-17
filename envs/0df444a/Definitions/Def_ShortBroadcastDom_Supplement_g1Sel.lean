-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_g1Sel
-- name    : ShortBroadcastDom_Supplement_g1Sel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:40:18.678819+00:00
-- url     : https://prove2.me/theorems/f82523d2-030b-4897-aa11-2ad9e2fdc1e4
-- title:
--   The transformation of App. G.1: branch vertices $B$, $Z=N^2_G[B]$, $F$, $R_0$ and costs $c$
-- statement:
--   Let $G$ be a finite graph and call a vertex of degree at least three a **branch vertex**. Put
--
--   $$
--   B=\{v:\deg_G(v)\ge3\},\qquad Z=N^2_G[B],\qquad F=V(G)\setminus Z,\qquad R_0=Z\setminus N_G[F],
--   $$
--
--   where $N^2_G[B]$ is the set of vertices at distance at most two from $B$. The selected set is $F$ (the vertices at distance at least three from every branch vertex), the demands are $R_0$, every vertex of $Z$ is a candidate, and the cost of a candidate is
--
--   $$
--   c(v)=3-|N_G(v)\cap F|\qquad(v\in Z).
--   $$
--
--   This is the first selection used for the exact coefficient three at subgraph density below $8/7$.
--
--   **Formalization Note** $N^2_G[B]$ is written as $N_G[N_G[B]]$, which avoids graph distance between components; the cost is computed in $\mathbb R$ and only its values on $Z$ are used.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. G.1, p.89 (PDF p.92)

import Mathlib
import Definitions.Def_ShortBroadcastDom_closedNbhd

namespace ShortBroadcastDom.Supplement

/-- The branch vertices `B = {v : deg_G(v) ≥ 3}` (App. G.1, p.89, PDF 92: "call a vertex of degree at
least three a branch vertex. Put B = {v : degG(v) ≥ 3}"). -/
def branchSet {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ.filter fun v => 3 ≤ G.degree v

/-- `Z = N²_G[B]`, the vertices at distance at most two from a branch vertex (p.89: "N²_G[B] is the
set of vertices at distance at most two from B").

**Formalization Note** `v ∈ N²[B]` iff `v ∈ N[w]` for some `w ∈ N[u]`, `u ∈ B`; this covers the
distances `0`, `1` and `2` and avoids `SimpleGraph.dist`, which is `0` between different components. -/
def g1Z {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ.filter fun v => ∃ u ∈ branchSet G, ∃ w ∈ closedNbhd G u, v ∈ closedNbhd G w

/-- **The selected set `F = V(G) \ Z` of the §G.1 transformation**: the vertices at distance at
least three from every branch vertex.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), App. G.1, p.89 (PDF 92): "Put B = {v : degG(v) ≥ 3}, Z = N²_G[B], F = V(G) \ Z,
R0 = Z \ NG[F] … The algorithm selects F and keeps R0 as demands. Every vertex of Z is a candidate,
with the cost c(v) = 3 − |NG(v) ∩ F| (v ∈ Z)." -/
def g1F {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ \ g1Z G

/-- The demands `R₀ = Z \ N_G[F]` of the §G.1 transformation (p.89). -/
def g1R0 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  (g1Z G).filter fun v => ∀ u ∈ g1F G, v ∉ closedNbhd G u

/-- The candidate costs `c(v) = 3 − |N_G(v) ∩ F|` (`v ∈ Z`) of the §G.1 transformation (p.89).

**Formalization Note** Computed in `ℝ` (no truncated subtraction); only its values on `Z` are used.
Lemma G.1(ii) shows `1 ≤ c(v) ≤ 3` on `Z`. -/
noncomputable def g1Cost {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : ℝ :=
  3 - ((G.neighborFinset v ∩ g1F G).card : ℝ)

end ShortBroadcastDom.Supplement


