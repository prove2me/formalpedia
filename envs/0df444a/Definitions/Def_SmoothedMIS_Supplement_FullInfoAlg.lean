-- Prove2me | Definitions.Def_SmoothedMIS_Supplement_FullInfoAlg
-- name    : SmoothedMIS_Supplement_FullInfoAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:38:32.669784+00:00
-- url     : https://prove2.me/theorems/4fe70ee9-c115-4e12-8de7-f1bd694122b3
-- title:
--   $T$-round randomized LOCAL algorithms with full information (radius-$T$ views)
-- statement:
--   Fix $n$ and a round budget $T\in\mathbb N$. The vertices are $[n]$, and their names serve as identifiers. A situation is a triple $(H,G,\tau)$: the communication graph $H$ (the smoothed graph), the base graph $G$, and the private tapes $\tau_u\in\{0,1\}^{\mathbb N}$ of the nodes.
--
--   Two situations $(H,G,\tau)$ and $(H',G',\tau')$ give node $v$ the **same radius-$T$ view** if
--   1. the balls agree: $\mathrm{dist}_H(v,u)\le T \iff \mathrm{dist}_{H'}(v,u)\le T$ for every $u$;
--   2. for all $a,b$ in this ball, $a\sim_H b \iff a\sim_{H'} b$ and $a\sim_G b\iff a\sim_{G'} b$;
--   3. $\tau_u=\tau'_u$ for every $u$ in the ball.
--
--   A **$T$-round randomized LOCAL algorithm with full information** assigns to each node $v$ an output bit $\mathrm{out}_v(H,G,\tau)\in\{0,1\}$ such that
--   $$
--   \text{same radius-}T\text{ view of }v \implies \mathrm{out}_v(H,G,\tau)=\mathrm{out}_v(H',G',\tau'),
--   $$
--   and such that $\tau\mapsto \mathrm{out}_v(H,G,\tau)$ is measurable for fixed $H, G$. Its output set is $\{v:\mathrm{out}_v(H,G,\tau)=1\}$.
--
--   This is the algorithm class of the lower bounds (Theorems 5.1 and 5.8). In the LOCAL model, messages are unbounded and local computation is unrestricted, so after $T$ rounds a node knows at most its radius-$T$ view, and $T+1$ rounds reveal all of it. The class also covers the extra knowledge the theorems grant: $n$ and $p$ (the rule is chosen per $n$), identifiers exactly in $[n]$, and whether each edge belongs to the base graph.
--
--   **Formalization Note** Distances are `SimpleGraph.edist` ($\infty$ between components). The view includes the edges between two vertices at distance exactly $T$, which a $T$-round execution does not see. This changes a round bound by at most one round.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §1.5 Distributed Computing Model, p.5 (PDF p.7); lower-bound model of Theorems 5.1 and 5.8, p.30 (PDF p.32) and p.39 (PDF p.41)

import Mathlib

open MeasureTheory

namespace SmoothedMIS.Supplement

/-- **Equal radius-`T` views.** Node `v` sees the same thing after `T` rounds in the two
situations `(H, G, τ)` and `(H', G', τ')`, where `H` is the communication (smoothed) graph, `G`
the base graph and `τ` the nodes' private random tapes: the vertices at `H`-distance at most `T`
from `v` are the same, on every pair of such vertices the `H`-adjacency and the `G`-adjacency
agree, and the tapes of these vertices agree (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed
Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), §1.5, p.5, and §5, p.30).

**Formalization Note** Distances are `SimpleGraph.edist` (`⊤` between components). The view
contains the vertex names (`Fin n`, the identifiers "exactly in `[n]`"), all edges of `H` between
two vertices of the ball (including edges between two vertices at distance exactly `T`), and the
`G`-adjacency of every such pair: for an edge of `H` whether it is an edge of `G`, and, for
symmetric-difference smoothing, also which pairs of the ball were edges of `G` deleted by the
smoothing. -/
def SameView {n : ℕ} (T : ℕ) (v : Fin n)
    (H G : SimpleGraph (Fin n)) (τ : Fin n → ℕ → Bool)
    (H' G' : SimpleGraph (Fin n)) (τ' : Fin n → ℕ → Bool) : Prop :=
  (∀ u, H.edist v u ≤ (T : ℕ∞) ↔ H'.edist v u ≤ (T : ℕ∞)) ∧
  (∀ a b, H.edist v a ≤ (T : ℕ∞) → H.edist v b ≤ (T : ℕ∞) →
    ((H.Adj a b ↔ H'.Adj a b) ∧ (G.Adj a b ↔ G'.Adj a b))) ∧
  (∀ u, H.edist v u ≤ (T : ℕ∞) → τ u = τ' u)

/-- **A `T`-round randomized LOCAL algorithm with full information** on the vertex set `Fin n`
(Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for Distributed MIS* (manuscript,
sha256 dc2131db…), §1.5 "Distributed Computing Model", p.5, and the lower-bound model of §5,
Theorems 5.1 and 5.8, pp.30 and 39).

`out v H G τ` is the output bit of node `v` when the communication graph is `H`, the base graph
is `G` and the nodes' private random tapes are `τ`. It may be any function of the information
that `v` can have gathered after `T` rounds of the LOCAL model: it depends on `(H, G, τ)` only
through the radius-`T` view of `v` (`SameView`). For each fixed `(H, G)` it is measurable in the
tapes.

**Formalization Note** The algorithm is a structure for one `n` and one budget `T`: it is chosen
after `n`, so it knows `n` and the smoothing parameter `p(n)`. Nodes are named by `Fin n`, which
are their identifiers ("IDs exactly in `[n]`"). Messages are unbounded and local computation is
unrestricted, so after `T` rounds a node can know everything in its radius-`T` view; the view
used here (all edges inside the radius-`T` ball, with their `G`-labels) is at most what `T + 1`
LOCAL rounds reveal, which changes a round bound by at most one round. Every `T`-round LOCAL
algorithm in which nodes know `n`, `p`, their identifiers and which incident edges belong to `G`
is an instance. -/
structure FullInfoAlg (n T : ℕ) where
  /-- output bit of a node, from the communication graph, the base graph and the tapes -/
  out : Fin n → SimpleGraph (Fin n) → SimpleGraph (Fin n) → (Fin n → ℕ → Bool) → Bool
  /-- locality: the output depends only on the radius-`T` view -/
  local_view : ∀ v H G τ H' G' τ', SameView T v H G τ H' G' τ' → out v H G τ = out v H' G' τ'
  /-- the output is measurable in the private randomness -/
  measurable_out : ∀ v H G, Measurable fun τ => out v H G τ

/-- The set the algorithm outputs: the nodes whose output bit is `true`. -/
def FullInfoAlg.outSet {n T : ℕ} (A : FullInfoAlg n T) (H G : SimpleGraph (Fin n))
    (τ : Fin n → ℕ → Bool) : Set (Fin n) :=
  {v | A.out v H G τ = true}

end SmoothedMIS.Supplement


