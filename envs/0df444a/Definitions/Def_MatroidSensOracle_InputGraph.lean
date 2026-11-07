-- Prove2me | Definitions.Def_MatroidSensOracle_InputGraph
-- name    : MatroidSensOracle_InputGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:47.521648+00:00
-- url     : https://prove2.me/theorems/9a48de1b-ebaf-46e6-85be-b6546c6d21d5
-- title:
--   Input graphs $G$, update sets $U=(I,F)$ and the multigraph $G+U$; the buffered graph $\mathcal G$ and the rerouting graphs $\mathcal G^*_h$, $\mathcal U^*$, $\mathcal G^*$
-- statement:
--   An **input graph** has vertices $V=\{0,\dots,n-1\}$, an edge set $E\subseteq V\times V$ and integer costs on $E$. An **update set** $U=(I,F)$ consists of deletions $F\subseteq E$ and a list $I$ of inserted edges with costs, and $|U|=|I|+|F|$. The updated graph
--   $$G+U = (V,(E\setminus F)\cup I)$$
--   is a **multigraph**: an inserted edge is a new edge, parallel to an existing one if the pair is already in $E$. The preprocessing reads $n,f,W,s,t,|E|$ and the edges with their costs (lexicographically); a query reads $|I|$, the inserted edges, $|F|$ and the deleted pairs.
--
--   For the rerouting reduction of §5.2:
--   1. $\mathcal G$ is $G$ with $2f$ zero-cost parallel $(s,t)$-edges (the buffer edges) appended.
--   2. For an $(s,t)$-flow $h$ of a multigraph $\mathcal G$, $\mathcal G^*_h$ is the residual graph $\mathcal G_h$ with two isolated vertices $s^*$ and $t^*$ added.
--   3. For an update $U=(I,F)$ of $\mathcal G$, with $F_h=\{e\in F:h(e)=1\}$,
--   $$\mathcal U^*=\bigl(I\cup\{(s^*,x),(y,t^*):(x,y)\in F_h\},\ (F\setminus F_h)\cup\{e^{\mathrm{rev}}:e\in F_h\}\bigr),\qquad \mathcal G^*=\mathcal G^*_h+\mathcal U^*,$$
--   with one new zero-cost edge $(s^*,x)$ and one $(y,t^*)$ per member $(x,y)$ of $F_h$.
--
--   **Formalization Note** In the residual graph the edge index $e$ stands for $e$ or $e^{\mathrm{rev}}$, so the deleted set of $\mathcal U^*$ is the index set $F$ itself. $\mathcal G^*$ has vertex set $V\sqcup\{s^*,t^*\}$.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §2, p.12 (PDF p.15); §5.2, pp.27–28 (PDF pp.30–31)

import Mathlib
import Definitions.Def_MatroidSensOracle_CostMultigraph

set_option autoImplicit false

namespace MatroidSensOracle

/-!
# Input graphs, update sets `G + U`, their word encodings, and the §5.2 graphs `𝒢`, `𝒢∗_h`, `𝒢∗`

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), §2, p.12 (PDF p.15):
"For an update set U = (I, F) of edge updates consisting of a set I of edge insertions and a set
F ⊆ E of edge deletions, with |U| = |I| + |F| ⩽ f, we denote by G + U := (V, (E \ F) ∪ I) the graph
obtained by applying the updates in U to G." §5.2, pp.27–28 (PDF pp.30–31): "we augment G to a graph
𝒢 by adding 2f zero-cost parallel (s, t)-edges […]. We construct an auxiliary multigraph 𝒢∗_h from the
residual graph 𝒢_h by adjoining a dummy source s∗ and a dummy sink t∗, both initially isolated. […]
𝒰∗ := (I ∪ {(s∗, x), (y, t∗) : (x, y) ∈ F_h}, (F \ F_h) ∪ {e_rev : e ∈ F_h}) […]. Let 𝒢∗ := 𝒢∗_h + 𝒰∗."

**Formalization Note.**
* The input graph is simple: vertices `Fin n`, an edge set `E ⊆ V × V` (loops are not excluded) and
  costs `c : V × V → ℤ`, read on `E`.
* An update `U = (I, F)` deletes `F ⊆ E` and inserts the list `I` of triples `(u, v, cost)`.
  `G + U` is the **multigraph** with edges `(E \ F)` followed by `I`: an inserted pair already present
  becomes a parallel edge, and repeated insertions are distinct edges. `|U| = |I| + |F|`.
* Edges of a set `E ⊆ V × V` are listed in lexicographic order (`pairList`); this order fixes the
  word encodings of instances and queries.
* `𝒢 = buffered G s t f` is `G` followed by `2f` zero-cost `(s, t)`-edges; the buffer edges are the
  last `2f` indices.
* `𝒢∗` lives on the vertices `Fin n ⊕ Bool`, with `s∗ = inr false` and `t∗ = inr true`. In the residual
  graph edge index `e` stands for `e` or `e_rev`, so the deleted set `(F \ F_h) ∪ {e_rev : e ∈ F_h}` of
  `𝒰∗` is the index set `F` itself. The inserted edges `(s∗, x), (y, t∗)` are one new zero-cost edge per
  member `(x, y)` of `F_h`, in index order (parallel edges when tails or heads repeat).
-/

/-- A simple directed input graph on `Fin n` with integer edge costs. -/
structure InputGraph (n : ℕ) where
  E : Finset (Fin n × Fin n)
  cost : Fin n × Fin n → ℤ

/-- An update set `U = (I, F)`: insertions `I` (as `(tail, head, cost)`) and deletions `F`. -/
structure Update (n : ℕ) where
  ins : List (Fin n × Fin n × ℤ)
  del : Finset (Fin n × Fin n)

/-- `|U| = |I| + |F|`. -/
def Update.size {n : ℕ} (U : Update n) : ℕ := U.ins.length + U.del.card

/-- The pairs of `E` in lexicographic order. -/
def pairList (n : ℕ) (E : Finset (Fin n × Fin n)) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    (List.finRange n).filterMap fun v => if (u, v) ∈ E then some (u, v) else none

namespace InputGraph

variable {n : ℕ}

/-- All costs on `E` lie in `[−W, W]`. -/
def CostsBounded (G : InputGraph n) (W : ℕ) : Prop := ∀ e ∈ G.E, |G.cost e| ≤ W

/-- `U` is a valid update set of size at most `f` with costs in `[−W, W]`: `F ⊆ E`, `|I| + |F| ≤ f`. -/
def ValidUpdate (G : InputGraph n) (f W : ℕ) (U : Update n) : Prop :=
  U.del ⊆ G.E ∧ U.size ≤ f ∧ ∀ x ∈ U.ins, |x.2.2| ≤ W

/-- `G + U` as a multigraph: the edges of `E \ F` (lexicographically), then the inserted edges. -/
def plus (G : InputGraph n) (U : Update n) : CostMultigraph (Fin n) :=
  CostMultigraph.ofList ((pairList n (G.E \ U.del)).map (fun e => (e.1, e.2, G.cost e)) ++ U.ins)

/-- `G` itself as a multigraph. -/
def toMultigraph (G : InputGraph n) : CostMultigraph (Fin n) := G.plus ⟨[], ∅⟩

/-- The input words of the preprocessing: `n, f, W, s, t, m`, then `tail, head, cost` of each edge. -/
def encode (G : InputGraph n) (f W : ℕ) (s t : Fin n) : List ℤ :=
  [(n : ℤ), f, W, (s : ℕ), (t : ℕ), (pairList n G.E).length] ++
    (pairList n G.E).flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ), G.cost e]

end InputGraph

/-- The query words of `U`: `|I|`, then `tail, head, cost` of each insertion, then `|F|`, then
`tail, head` of each deletion (lexicographically). -/
def Update.encode {n : ℕ} (U : Update n) : List ℤ :=
  [(U.ins.length : ℤ)] ++ U.ins.flatMap (fun x => [((x.1 : ℕ) : ℤ), ((x.2.1 : ℕ) : ℤ), x.2.2]) ++
    [((pairList n U.del).length : ℤ)] ++
    (pairList n U.del).flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)]

/-- `H` with `r` zero-cost parallel `(s, t)`-edges appended (the buffer edges, indices `≥ H.m`). -/
def CostMultigraph.addParallel {V : Type} (H : CostMultigraph V) (s t : V) (r : ℕ) :
    CostMultigraph V :=
  H.addEdges (List.replicate r (s, t, 0))

/-- The buffered graph `𝒢`: `G` with `2f` zero-cost parallel `(s, t)`-edges. -/
def InputGraph.buffered {n : ℕ} (G : InputGraph n) (s t : Fin n) (f : ℕ) : CostMultigraph (Fin n) :=
  G.toMultigraph.addParallel s t (2 * f)

/-- The number of buffer edges (indices `≥ m₀`) carrying flow under `g`. -/
def bufferUse {V : Type} (H : CostMultigraph V) (m₀ : ℕ) (g : Fin H.m → Bool) : ℕ :=
  (Finset.univ.filter fun e : Fin H.m => m₀ ≤ (e : ℕ) ∧ g e = true).card

/-- The dummy source `s∗`. -/
def sStar (n : ℕ) : Fin n ⊕ Bool := Sum.inr false

/-- The dummy sink `t∗`. -/
def tStar (n : ℕ) : Fin n ⊕ Bool := Sum.inr true

/-- `𝒢∗_h`: the residual graph `𝒢_h` with two isolated dummy vertices `s∗`, `t∗` adjoined. -/
def starResidual {n : ℕ} (H : CostMultigraph (Fin n)) (h : Fin H.m → Bool) :
    CostMultigraph (Fin n ⊕ Bool) :=
  (H.residual h).mapVert Sum.inl

/-- The insertions `I∗` of `𝒰∗`: the edges of `I`, then for each deleted flow edge `(x, y) ∈ F_h`
(in index order) a zero-cost edge `(s∗, x)` and a zero-cost edge `(y, t∗)`. -/
def starInsertions {n : ℕ} (H : CostMultigraph (Fin n)) (h : Fin H.m → Bool)
    (I : List (Fin n × Fin n × ℤ)) (F : Finset (Fin H.m)) : List ((Fin n ⊕ Bool) × (Fin n ⊕ Bool) × ℤ) :=
  I.map (fun x => (Sum.inl x.1, Sum.inl x.2.1, x.2.2)) ++
    ((List.finRange H.m).filter fun e => e ∈ F ∧ h e = true).flatMap fun e =>
      [(sStar n, Sum.inl (H.arcs.tail e), 0), (Sum.inl (H.arcs.head e), tStar n, 0)]

/-- `𝒢∗ = 𝒢∗_h + 𝒰∗` for the update `(I, F)` of `H` and the flow `h`: delete the residual edges with
index in `F` (these are `F \ F_h` and `{e_rev : e ∈ F_h}`) and insert `I∗`. -/
def starGraph {n : ℕ} (H : CostMultigraph (Fin n)) (h : Fin H.m → Bool)
    (I : List (Fin n × Fin n × ℤ)) (F : Finset (Fin H.m)) : CostMultigraph (Fin n ⊕ Bool) :=
  (starResidual H h).apply (starInsertions H h I F) F

end MatroidSensOracle


