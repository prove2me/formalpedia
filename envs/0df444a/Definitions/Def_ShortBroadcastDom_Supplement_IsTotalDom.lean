-- Prove2me | Definitions.Def_ShortBroadcastDom_Supplement_IsTotalDom
-- name    : ShortBroadcastDom_Supplement_IsTotalDom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:39:38.723961+00:00
-- url     : https://prove2.me/theorems/e799fa3f-cfbe-470b-8f3c-32d8525219bb
-- title:
--   Isolate-free graphs, total dominating sets and $\gamma_{t,f}(G)$
-- statement:
--   A graph $G$ is **isolate-free** if no vertex is isolated. A set $D$ of vertices is a **total dominating set** if every vertex of $G$, whether it belongs to $D$ or not, has a neighbour in $D$; such a set exists exactly when $G$ is isolate-free. The **fractional total domination number** is
--
--   $$
--   \gamma_{t,f}(G)=\min\Bigl\{\sum_v y_v\;:\;y\ge0,\ \sum_{u\in N_G(v)}y_u\ge1\text{ for every vertex }v\Bigr\},
--   $$
--
--   the covering optimum $\tau_c$ with demands $V(G)$, covering sets the open neighbourhoods and unit costs.
--
--   These are the objects of the total-domination results (Theorems F.1, F.12, G.17).
--
--   **Formalization Note** $\gamma_{t,f}$ is `tauRel` with $C(v)=N_G(v)$; the paper defines it only on isolate-free graphs, where the program is feasible, and every statement using it assumes isolate-freeness.
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. F, pp.76–77 (PDF pp.79–80); App. F.7, p.86 (PDF p.89)

import Mathlib
import Definitions.Def_ShortBroadcastDom_Supplement_tauRel

namespace ShortBroadcastDom.Supplement

/-- `IsolateFree G`: no vertex of `G` is isolated (every vertex has a neighbour).

Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), App. F, p.76 (PDF 79): "Such a set exists exactly when G has no isolated vertex, and G
is then called isolate-free." -/
def IsolateFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v, ∃ u, G.Adj v u

/-- **Total domination.** `IsTotalDom G D`: every vertex of `G`, whether it belongs to `D` or not,
has a neighbour in `D`.

App. F, p.76 (PDF 79): "A set D is a total dominating set of a graph G if every vertex of G,
whether it belongs to D or not, has a neighbor in D." -/
def IsTotalDom {V : Type} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ u ∈ D, G.Adj v u

/-- **The fractional total domination number `γ_{t,f}(G)`**: the minimum of `∑_v y_v` over all
`y ≥ 0` with `∑_{u ∈ N(v)} y_u ≥ 1` for every vertex `v`, i.e. `τ_c` with demands `V(G)`, covering
sets the open neighbourhoods `C(v) = N_G(v)` and unit costs.

App. F, pp.76–77 (PDF 79–80): "The fractional total domination number γt,f(G) is the minimum of
∑_v yv over all y ≥ 0 with ∑_{u∈N(v)} yu ≥ 1 for every vertex v"; App. F.7, p.86 (PDF 89).

**Formalization Note** `γ_{t,f}(G) = tauRel V(G) N_G 1`. On an isolate-free graph the program is
feasible and the `sInf` is the minimum; the paper defines `γ_{t,f}` only on isolate-free graphs, and
every statement of the mission that uses it assumes `IsolateFree G`. -/
noncomputable def totFracDom {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  tauRel Finset.univ (fun v => G.neighborFinset v) (fun _ => 1)

end ShortBroadcastDom.Supplement


