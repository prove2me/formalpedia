-- Prove2me | Definitions.Def_DecrNearAddAPSP_W2_MonoES
-- name    : DecrNearAddAPSP_W2_MonoES
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:11:09.554667+00:00
-- url     : https://prove2.me/theorems/a3a56db2-77d0-478a-9d79-e214755e1dcd
-- title:
--   Monotone Even–Shiloach tree levels as a least fixed point, directed paths, and the dynamic input of a monotone ES-tree
-- statement:
--   **Directed weighted graphs.** $H(x,v)\in\mathbb N\cup\{\infty\}$ is the weight of the edge $x\to v$ ($\infty$: no edge). An undirected weighted graph $G$ gives the symmetric $H(x,v)=w(x,v)$ on edges. A **path** from $u$ to $v$ in $H$ is a list of distinct vertices starting at $u$ and ending at $v$ whose consecutive pairs are edges; its weight is the sum of those edge weights.
--
--   **Monotone ES-tree levels** (pp. 7–8). For a dynamic graph $H_0,H_1,\dots$ (edges may be inserted, deleted, made heavier or lighter), a root $s$ and a depth $\tau$: a level function $\ell:V\to\mathbb N\cup\{\infty\}$ is **admissible above $L$** for $H$ if
--   $$
--   \ell(s)=0,\qquad \ell(v)\ \ge\ \min_{x}\big(\ell(x)+H(x,v)\big)\ \ (v\ne s),\qquad \ell(v)\in\{0,\dots,\tau\}\cup\{\infty\},\qquad \ell\ge L .
--   $$
--   The levels are $\ell_0=$ the least admissible function for $H_0$ (above $0$), and $\ell_t=$ the least admissible function for $H_t$ above $\ell_{t-1}$. The admissible set contains the function that is $0$ at $s$ and $\infty$ elsewhere and is closed under pointwise minima, so the least element exists. This is the page's operational description: an inserted or lighter edge is registered without the relaxation step, $\ell(v)$ increases only when every incoming edge fails $\ell(z)+w(z,v)\le\ell(v)$, the invariant $\ell(v)\ge\min_{(x,v)}\{\ell(x)+w(x,v)\}$ holds, and levels above $\tau$ mean "disconnected".
--
--   **Dynamic input of Lemma 2.5.** The auxiliary graph $H$ undergoes insertions of a new edge with weight $c\in[1,W]$, deletions, and weight increases to $c\le W$. A program receives $n$, the root $s$, the depth $\tau$, the edge count and the edges $u,v,w(u,v)$ of $H_0$; then each update as $0,u,v,c$ (insert), $1,u,v$ (delete) or $2,u,v,c$ (increase). It reports levels by writing pairs $v,q$ (set $\ell(v)$ to $\infty$ if $q=0$, else to $q-1$), replayed from all levels $\infty$. $E(H)$ is the number of distinct pairs that are an edge of some $H_t$, and $W(H)$ the number of updates.
--
--   **Formalization Note** `monoLevels H s τ t` is defined as the pointwise infimum of the admissible functions, recursively in $t$; `IsDPath` and `dWeight` are paths and their weights in a directed graph `DGraph β := β → β → ℕ∞`.
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), pp. 7–8, §2 (Monotone Even-Shiloach Trees), Lemmas 2.4 and 2.5

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Run

namespace DecrNearAddAPSP.W2

/-! # Monotone Even–Shiloach tree levels, and the fully dynamic input of a monotone ES-tree

Koveshi, Roditty, Sapir, *First Near-Additive All-Pairs Approximate Shortest Paths in Decremental
Weighted Graphs*, arXiv:2611.04635 (PDF sha256 6bb2b230…), §2 "Monotone Even-Shiloach Trees",
pp. 7–8 (PDF 9–10), Lemmas 2.4 and 2.5.

**Formalization Note.**
* A weighted directed graph on `β` is `H : β → β → ℕ∞`, `H x v` the weight of the edge `x → v`
  (`∞` = no edge). An undirected weighted graph `G` gives the symmetric `G.toD`.
* The page describes the monotone ES-tree operationally: an inserted (or lighter) edge is
  registered without the relaxation step, a level `ℓ(v)` increases only when every incoming edge
  `(z, v)` fails `ℓ(z) + w(z, v) ≤ ℓ(v)`, the invariant `ℓ(v) ≥ min_{(x, v)} {ℓ(x) + w(x, v)}` holds,
  and levels above `τ` mean "disconnected" (`∞`). Its levels are the least fixed point: for a
  dynamic graph `H_0, H_1, …`, a root `s` and a depth `τ`, `ℓ_0` is the least `ℓ : β → ℕ∞` with
  `ℓ(s) = 0`, `ℓ(v) ≥ min_x (ℓ(x) + w_0(x, v))` for `v ≠ s`, and every `ℓ(v) ∈ {0, …, τ} ∪ {∞}`;
  `ℓ_t` is the least such `ℓ` for `H_t` with `ℓ ≥ ℓ_{t−1}` pointwise. The admissible set is
  nonempty (`∞` off the root) and, for finite `β`, closed under pointwise minima, so the pointwise
  infimum below is its least element.
* A path in a directed graph is a list of distinct vertices from `u` to `v` whose consecutive pairs
  are edges; its weight is the sum of those edge weights.
* Lemma 2.5's monotone ES-tree program receives `n`, the root `s`, the depth `τ`, the number of
  edges and the edges `u, v, w(uv)` of `H_0`, then each update: `0, u, v, c` inserts `{u, v}` with
  weight `c`, `1, u, v` deletes `{u, v}`, `2, u, v, c` raises the weight of `{u, v}` to `c`. Its level
  records are pairs `v, q` setting `ℓ(v)` to `∞` if `q = 0` and to `q − 1` otherwise, replayed from
  all levels `∞`. -/

/-- A weighted directed graph on `β`: `H x v` is the weight of the edge `x → v`, `∞` if absent. -/
abbrev DGraph (β : Type) := β → β → ℕ∞

open Classical in
/-- The symmetric directed graph of an undirected weighted graph: `x → v` has weight `w(x, v)` when
`{x, v}` is an edge, `∞` otherwise. -/
noncomputable def WGraph.toD {α : Type} (G : WGraph α) : DGraph α :=
  fun x v => if G.adj.Adj x v then (G.wt s(x, v) : ℕ∞) else ⊤

/-- The admissible level functions of a monotone ES-tree of `H` rooted at `s` up to depth `τ`, above
the previous levels `L`: `ℓ(s) = 0`; `ℓ(v) ≥ min_x (ℓ(x) + H(x, v))` for `v ≠ s`; every level is in
`{0, …, τ} ∪ {∞}`; and `ℓ ≥ L` pointwise. -/
def LevelAdmissible {β : Type} (H : DGraph β) (s : β) (τ : ℕ) (L : β → ℕ∞) (ℓ : β → ℕ∞) :
    Prop :=
  ℓ s = 0 ∧ (∀ v, v ≠ s → ⨅ x, (ℓ x + H x v) ≤ ℓ v) ∧ (∀ v, ℓ v ≤ τ ∨ ℓ v = ⊤) ∧
    ∀ v, L v ≤ ℓ v

/-- The least admissible level function (pointwise infimum of the admissible ones). -/
noncomputable def leastLevels {β : Type} (H : DGraph β) (s : β) (τ : ℕ) (L : β → ℕ∞) :
    β → ℕ∞ :=
  fun v => ⨅ (ℓ : β → ℕ∞) (_ : LevelAdmissible H s τ L ℓ), ℓ v

/-- The levels `ℓ_t` of a monotone ES-tree of the dynamic graph `H_0, H_1, …` rooted at `s`,
maintained up to depth `τ`: `ℓ_0` is the least admissible level function of `H_0`, and `ℓ_{t+1}` the
least admissible one of `H_{t+1}` above `ℓ_t`. -/
noncomputable def monoLevels {β : Type} (H : ℕ → DGraph β) (s : β) (τ : ℕ) : ℕ → β → ℕ∞
  | 0 => leastLevels (H 0) s τ (fun _ => 0)
  | t + 1 => leastLevels (H (t + 1)) s τ (monoLevels H s τ t)

/-- The weight of a vertex list in `H`: the sum of `H(x, y)` over consecutive pairs `x, y`. -/
def dWeight {β : Type} (H : DGraph β) (l : List β) : ℕ∞ :=
  ((l.zip l.tail).map fun p => H p.1 p.2).sum

/-- `l` is a path from `u` to `v` in the directed graph `H`: it starts at `u`, ends at `v`, repeats
no vertex, and every consecutive pair is an edge (finite weight). -/
def IsDPath {β : Type} (H : DGraph β) (u v : β) (l : List β) : Prop :=
  l.head? = some u ∧ l.getLast? = some v ∧ l.Nodup ∧ ∀ p ∈ l.zip l.tail, H p.1 p.2 ≠ ⊤

/-- An update of the auxiliary graph `H` of Lemma 2.5: insert the edge `{u, v}` with weight `c`,
delete `{u, v}`, or raise the weight of `{u, v}` to `c`. -/
inductive ESUpd (n : ℕ) where
  | ins (u v : Fin n) (c : ℕ)
  | del (u v : Fin n)
  | inc (u v : Fin n) (c : ℕ)

/-- The graph after an update of `H`. -/
def ESUpd.apply {n : ℕ} (G : WGraph (Fin n)) : ESUpd n → WGraph (Fin n)
  | .ins u v c => ⟨G.adj ⊔ SimpleGraph.edge u v, Function.update G.wt s(u, v) c⟩
  | .del u v => ⟨G.adj.deleteEdges {s(u, v)}, G.wt⟩
  | .inc u v c => ⟨G.adj, Function.update G.wt s(u, v) c⟩

/-- A legal update of `H` with weights in `[1, W]`: an insertion adds a new edge `{u, v}`, `u ≠ v`,
with weight `c ∈ [1, W]`; a deletion removes a present edge; a weight increase raises the weight of
a present edge to `c` with `w(u, v) < c ≤ W`. -/
def ESUpd.IsLegal {n : ℕ} (W : ℕ) (G : WGraph (Fin n)) : ESUpd n → Prop
  | .ins u v c => u ≠ v ∧ ¬ G.adj.Adj u v ∧ 1 ≤ c ∧ c ≤ W
  | .del u v => G.adj.Adj u v
  | .inc u v c => G.adj.Adj u v ∧ G.wt s(u, v) < c ∧ c ≤ W

/-- Every update of the list is legal for the graph it meets, starting from `G`. -/
def IsLegalESSeq {n : ℕ} (W : ℕ) : WGraph (Fin n) → List (ESUpd n) → Prop
  | _, [] => True
  | G, x :: ρ => x.IsLegal W G ∧ IsLegalESSeq W (x.apply G) ρ

/-- `H_t`: the auxiliary graph after the first `t` updates of `ρ`. -/
def esGraphAt {n : ℕ} (H₀ : WGraph (Fin n)) (ρ : List (ESUpd n)) (t : ℕ) : WGraph (Fin n) :=
  (ρ.take t).foldl ESUpd.apply H₀

/-- The words of an update of `H`: `0, u, v, c` inserts, `1, u, v` deletes, `2, u, v, c` raises the
weight to `c`. -/
def ESUpd.words {n : ℕ} : ESUpd n → List ℕ
  | .ins u v c => [0, u.val, v.val, c]
  | .del u v => [1, u.val, v.val]
  | .inc u v c => [2, u.val, v.val, c]

/-- The initialization words of a monotone ES-tree: `n`, the root `s`, the depth `τ`, the number of
edges, and every edge of `H_0` as `u, v, w(uv)`. -/
def esInitWords {n : ℕ} (s : Fin n) (τ : ℕ) (H₀ : WGraph (Fin n)) (es : List (Fin n × Fin n)) :
    List ℕ :=
  [n, s.val, τ, es.length] ++ es.flatMap fun e => [e.1.val, e.2.val, H₀.wt s(e.1, e.2)]

/-- Replay level records: the pair `v, q` sets `ℓ(v)` to `decodeEst q` when `v` is a vertex; any
other pair is skipped, as is a single trailing word. -/
def replayLevels {n : ℕ} : (Fin n → ℕ∞) → List ℕ → (Fin n → ℕ∞)
  | ℓ, v :: q :: rest =>
      replayLevels (if h : v < n then Function.update ℓ ⟨v, h⟩ (decodeEst q) else ℓ) rest
  | ℓ, _ => ℓ

/-- The levels the program maintains at time `t`: every level record written up to the completed
state at time `t`, replayed from all levels `∞`. -/
noncomputable def levelsAt (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) {n : ℕ} (s : Fin n)
    (τ : ℕ) (H₀ : WGraph (Fin n)) (es : List (Fin n × Fin n)) (ρ : List (ESUpd n)) (t : ℕ) :
    Fin n → ℕ∞ :=
  replayLevels (fun _ => ⊤) (outputAt P ω (esInitWords s τ H₀ es) (ρ.map ESUpd.words) t)

/-- The total time of a monotone ES-tree run: initialization and every update of `ρ`. -/
noncomputable def esTime (P : DynBrooks.Program) {w : ℕ} (ω : ℕ → BitVec w) {n : ℕ} (s : Fin n)
    (τ : ℕ) (H₀ : WGraph (Fin n)) (es : List (Fin n × Fin n)) (ρ : List (ESUpd n)) : ℕ∞ :=
  totalTime P ω (esInitWords s τ H₀ es) (ρ.map ESUpd.words)

open Classical in
/-- `E(H)`: the number of distinct vertex pairs that are an edge of some `H_t`, `0 ≤ t ≤ |ρ|`. -/
noncomputable def everEdges {n : ℕ} (H₀ : WGraph (Fin n)) (ρ : List (ESUpd n)) : ℕ :=
  (Finset.univ.filter fun e : Sym2 (Fin n) =>
    ∃ t ≤ ρ.length, e ∈ (esGraphAt H₀ ρ t).adj.edgeSet).card

end DecrNearAddAPSP.W2


