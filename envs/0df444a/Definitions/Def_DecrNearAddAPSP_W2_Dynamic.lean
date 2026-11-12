-- Prove2me | Definitions.Def_DecrNearAddAPSP_W2_Dynamic
-- name    : DecrNearAddAPSP_W2_Dynamic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:05:33.858016+00:00
-- url     : https://prove2.me/theorems/25fcd935-38f5-4cae-818e-d09c1c9e6fd7
-- title:
--   Decremental update sequences (edge deletions and strict weight increases) and the graphs G_t
-- statement:
--   In the **decremental setting** (p. 7) a weighted graph $G_0$ on $V=\{0,\dots,n-1\}$ undergoes a finite sequence of updates, each of which either **deletes** a present edge $\{u,v\}$ or **increases the weight** of a present edge $\{u,v\}$ to an integer $c$ with $w(u,v)<c\le W$. The graph after the first $t$ updates is $G_t$; time $0$ is initialization. A **decremental instance with weight bound $W$** is an initial graph with integer weights in $[1,W]$ together with a sequence of legal updates of these two kinds, so that every $G_t$ has weights in $[1,W]$. The sequence is a fixed finite list, chosen independently of any randomness of an algorithm: this is the **oblivious adversary** of p. 7.
--
--   An **edge listing** of $G$ lists every edge of $G$ exactly once, in any order and orientation; it is how the initial graph is handed to a program.
--
--   These objects fix the input of the goal (Theorem 3) and of Lemmas 5.7 and 5.8.
--
--   **Formalization Note** `Upd n` has constructors `del u v` and `inc u v c` (set the weight of $\{u,v\}$ to $c$); `graphAt G₀ σ t` folds the first $t$ updates. Legality is checked against the graph each update meets.
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), p. 7, §2 (Dynamic Graphs and Adversary Models); p. 6 footnote 3

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs

namespace DecrNearAddAPSP.W2

/-! # Decremental update sequences and the graphs `G_t`

Koveshi, Roditty, Sapir, *First Near-Additive All-Pairs Approximate Shortest Paths in Decremental
Weighted Graphs*, arXiv:2611.04635 (PDF sha256 6bb2b230…), §2 "Dynamic Graphs and Adversary
Models", p. 7 (PDF 9); footnote 3, p. 6 (PDF 8).

**Formalization Note.** Vertices are `Fin n`. A decremental update (p. 7: "only edge deletions and
weight increases are permitted") deletes a present edge or raises the weight of a present edge to a
strictly larger integer. `G_t` is the graph after the first `t` updates (`G_0` the initial graph,
time `0` = initialization). An update sequence is a finite list fixed in advance, independently of
any randomness (the oblivious adversary, p. 7). -/

/-- A decremental update on `Fin n`: delete the edge `{u, v}`, or set the weight of the edge
`{u, v}` to `c`. -/
inductive Upd (n : ℕ) where
  | del (u v : Fin n)
  | inc (u v : Fin n) (c : ℕ)

/-- Whether an update is a deletion. -/
def Upd.isDel {n : ℕ} : Upd n → Bool
  | .del _ _ => true
  | .inc _ _ _ => false

/-- The graph after an update: a deletion removes the edge, a weight change sets its weight. -/
def Upd.apply {n : ℕ} (G : WGraph (Fin n)) : Upd n → WGraph (Fin n)
  | .del u v => ⟨G.adj.deleteEdges {s(u, v)}, G.wt⟩
  | .inc u v c => ⟨G.adj, Function.update G.wt s(u, v) c⟩

/-- `G_t`: the graph after the first `t` updates of `σ`, with `G_0 = G₀`. -/
def graphAt {n : ℕ} (G₀ : WGraph (Fin n)) (σ : List (Upd n)) (t : ℕ) : WGraph (Fin n) :=
  (σ.take t).foldl Upd.apply G₀

/-- A legal decremental update from `G` with weights capped at `W`: a deletion removes a present
edge; a weight increase raises the weight of a present edge to an integer `c` with
`w(u, v) < c ≤ W`. -/
def IsLegalUpd {n : ℕ} (W : ℕ) (G : WGraph (Fin n)) : Upd n → Prop
  | .del u v => G.adj.Adj u v
  | .inc u v c => G.adj.Adj u v ∧ G.wt s(u, v) < c ∧ c ≤ W

/-- Every update of the list is legal for the graph it meets, starting from `G`. -/
def IsLegalSeq {n : ℕ} (W : ℕ) : WGraph (Fin n) → List (Upd n) → Prop
  | _, [] => True
  | G, x :: σ => IsLegalUpd W G x ∧ IsLegalSeq W (x.apply G) σ

/-- A decremental instance with weight bound `W` (pp. 6–7, footnote 3): the initial graph has
integer weights in `[1, W]` and every update is a legal deletion or weight increase (weights stay
in `[1, W]`). -/
def IsDecrInstance {n : ℕ} (W : ℕ) (G₀ : WGraph (Fin n)) (σ : List (Upd n)) : Prop :=
  G₀.WeightsIn W ∧ IsLegalSeq W G₀ σ

/-- `es` lists each edge of `G` exactly once, in any order and orientation. -/
def IsEdgeListing {n : ℕ} (G : WGraph (Fin n)) (es : List (Fin n × Fin n)) : Prop :=
  (es.map fun e => s(e.1, e.2)).Nodup ∧
    ∀ e : Sym2 (Fin n), e ∈ G.adj.edgeSet ↔ e ∈ es.map fun e => s(e.1, e.2)

end DecrNearAddAPSP.W2


