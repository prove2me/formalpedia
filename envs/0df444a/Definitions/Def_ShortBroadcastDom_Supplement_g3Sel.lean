-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_g3Sel
-- name    : ShortBroadcastDom_Supplement_g3Sel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:41:28.687794+00:00
-- url     : https://prove2.me/theorems/00bf7633-fcef-4b8d-b650-df60bf109a99
-- title:
--   The transformation of App. G.3: $F_0$, $F$, $Z$, costs $c$, candidates $K$ and covering sets $N(r)\cap K$
-- statement:
--   Let $G$ be an isolate-free graph, $B=\{v:\deg_G(v)\ge3\}$ and $Z_0=N^2_G[B]$. Put $F_0=V(G)\setminus Z_0$, let $F$ be $F_0$ without the vertices that are isolated in $G[F_0]$, and $Z=V(G)\setminus F$. Every vertex receives the cost
--
--   $$
--   c(v)=2-|N_G(v)\cap F|,
--   $$
--
--   the candidates are $K=\{v:c(v)>0\}$, and every vertex of $Z$ is a demand, to be covered by a candidate in its open neighbourhood, i.e. $C(r)=N_G(r)\cap K$. The optimum of this program is $C^*=\tau_c$.
--
--   This is the first selection used for the exact coefficient two for total domination at subgraph density below $9/8$.
--
--   **Formalization Note** $B$ and $Z_0$ are the same sets as in App. G.1. The cost is computed in $\mathbb R$; on isolate-free graphs it takes values in $\{0,1,2\}$ (Lemma G.11).
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. G.3, p.96 (PDF p.99)

import Mathlib
import Definitions.Def_ShortBroadcastDom_Supplement_g1Sel

namespace ShortBroadcastDom.Supplement

/-- `F₀ = V(G) \ Z₀` with `Z₀ = N²_G[B]` (App. G.3, p.96, PDF 99). -/
def g3F0 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ \ g1Z G

open Classical in
/-- **The selected set `F` of the §G.3 transformation**: `F₀` without the vertices that are
isolated in `G[F₀]`.

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), App. G.3, p.96 (PDF 99): "Let G be isolate-free, and put B = {v : degG(v) ≥ 3},
Z0 = N²_G[B], F0 = V(G) \ Z0. Let F be F0 without the vertices that are isolated in G[F0], and put
Z = V(G) \ F. The algorithm selects F. Every vertex is given the cost c(v) = 2 − |N(v) ∩ F|, the
candidates are the vertices of K = {v : c(v) > 0}, and every vertex of Z is a demand, to be covered
by a candidate in its open neighborhood. Let C∗ be the optimum of this program and
C(x) = ∑_{v∈K} c(v)xv."

**Formalization Note** `B` and `Z₀ = N²_G[B]` are `branchSet` and `g1Z` (the same sets as in §G.1). -/
def g3F {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  (g3F0 G).filter fun v => ∃ u ∈ g3F0 G, G.Adj v u

/-- The demands `Z = V(G) \ F` of the §G.3 transformation (p.96). -/
def g3Z {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset V :=
  Finset.univ \ g3F G

/-- The costs `c(v) = 2 − |N(v) ∩ F|` of the §G.3 transformation, for every vertex (p.96).

**Formalization Note** Computed in `ℝ`. Lemma G.11(ii) shows `c(v) ∈ {0, 1, 2}` on every
isolate-free graph. -/
noncomputable def g3Cost {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) : ℝ :=
  2 - ((G.neighborFinset v ∩ g3F G).card : ℝ)

open Classical in
/-- The candidates `K = {v : c(v) > 0}` of the §G.3 transformation (p.96). -/
noncomputable def g3K {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 0 < g3Cost G v

/-- The covering sets of the §G.3 program: a demand `r ∈ Z` is covered by a candidate of `K` in its
open neighbourhood, `C(r) = N(r) ∩ K` (p.96). -/
noncomputable def g3Cov {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) : Finset V :=
  G.neighborFinset r ∩ g3K G

end ShortBroadcastDom.Supplement


