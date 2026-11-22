-- Prove2me | Definitions.Def_DecrNbhdCover_Supplement_TreeCover
-- name    : DecrNbhdCover_Supplement_TreeCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:31:12.111292+00:00
-- url     : https://prove2.me/theorems/13cd27ab-1aee-4694-b876-057c18617bf1
-- title:
--   Dominating tree embeddings (Definition 10.6) and the interface of the decremental tree cover (Theorem 10.7)
-- statement:
--   Let $G$ be a graph with positive integer lengths. A forest $T$ with positive integer lengths is a **tree embedding** of $G$ if $V(G)\subseteq V(T)$. It is a **dominating tree embedding** if, in addition,
--   $$\mathrm{dist}_T(u,v)\ge\mathrm{dist}_G(u,v)\qquad\text{for all }u,v\in V(G).$$
--
--   The interface of Theorem 10.7: the input is an $n$-vertex, $m$-edge graph $G$ under edge deletions, with largest edge length $L$. The algorithm reports a number $k$ once and maintains graphs $T_1,\dots,T_k$. With a function $f$ and a constant $C$, at all times:
--
--   1. $k\le C\log_2(2+n)\log_2(2+Ln)$;
--   2. every $T_i$ is a dominating tree embedding of the current $G$;
--   3. for all $u,v\in V(G)$ there is an index $i$ with $\mathrm{dist}_{T_i}(u,v)\le C(\log_2(2+n+m))^C\log_2(2+L)\cdot\mathrm{dist}_G(u,v)$.
--
--   The total update time is at most $C\,(m+n)^{1+f(m+n)}(\log_2(2+L))^C$.
--
--   **Formalization Note** Each $T_i$ is a reported dynamic graph; the paper does not restrict how the $T_i$ change, so every reported change is allowed. The vertices of $G$ keep their numbers in every $T_i$. A forest is a graph with no cycle, where two parallel edges form a cycle.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 10.6 and Theorem 10.7, p.82 (PDF 86)

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Common

set_option autoImplicit false

namespace DecrNbhdCover.Supplement

open DynConnWC
open scoped ENNReal

/-! # Dominating tree embeddings (Definition 10.6) and the decremental tree cover (Theorem 10.7)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 10.6 and Theorem 10.7, p.82 (PDF 86).

"Consider a graph G with integral lengths ℓG(e) > 0 on its edges e ∈ E(G). We say that a forest graph T with integral lengths ℓT(e) > 0 on
its edges e ∈ E(T) is a tree embedding of G if V(G) ⊆ V(T). If additionally distT(u, v) ≥ distG(u, v) holds for all pairs u, v ∈ V(G), then
we say that T is a dominating tree embedding of G."

**Formalization Note.** The vertices of `G` keep their numbers in every `T_i`; other vertices of `T_i` may carry any number. The program
reports the number `k` of graphs once, as `0, k`, and each graph `T_i` (`i < k`) as a reported dynamic graph: `1, i, (report)`. The paper
does not restrict how the `T_i` change, so every vertex and edge insertion and deletion is allowed, and each is reported. The only operation
is `0, e` (delete edge `e` of `G`); there are no queries. Input words: `n`, then the edge list. -/

/-- `T` is a dominating tree embedding of `G`: a forest containing `V(G)` with `distT(u, v) ≥ distG(u, v)` for all `u, v ∈ V(G)`. -/
structure IsDominatingTreeEmbedding (G T : Graph ℕ ℕ) : Prop where
  wf : T.WF
  forest : IsForest T
  sub : G.V ⊆ T.V
  dom : ∀ u ∈ G.V, ∀ v ∈ G.V, G.dist u v ≤ T.dist u v

/-- A report: the number of trees, or an update of tree `i`. -/
inductive TreeReport where
  | count (k : ℕ)
  | tree (i : ℕ) (r : DynReport)

/-- The words of a report. -/
def TreeReport.words : TreeReport → List ℕ
  | .count k => [0, k]
  | .tree i r => 1 :: i :: r.words

/-- The reported number of trees and the trees. -/
structure TreeState where
  k : Option ℕ
  trees : ℕ → DynState

/-- The effect of a report: `k` is reported once, and only trees `i < k` are updated. -/
noncomputable def treeStep (s : TreeState) : TreeReport → Option TreeState
  | .count k => match s.k with
    | none => some { s with k := some k }
    | some _ => none
  | .tree i r => match s.k with
    | some k => if i < k then ((s.trees i).step r).map (fun d => { s with trees := Function.update s.trees i d }) else none
    | none => none

/-- The protocol of Theorem 10.7; an operation is the number of a deleted edge. -/
noncomputable def treeProtocol : Protocol ℕ TreeReport TreeState where
  opWords := fun e => [0, e]
  isQuery := fun _ => false
  enc := TreeReport.words
  step := treeStep
  st₀ := ⟨none, fun _ => DynState.empty⟩

/-- The input of Theorem 10.7. -/
structure TreeInput where
  n : ℕ
  edges : List (ℕ × ℕ × ℕ)

namespace TreeInput

variable (I : TreeInput)

/-- The number of edges. -/
def m : ℕ := I.edges.length

/-- The largest edge length `L`. -/
def L : ℕ := maxWord (I.edges.map (fun t => t.2.2))

/-- The conditions of Theorem 10.7: `G` has at least one vertex. -/
structure Ok : Prop where
  n_pos : 1 ≤ I.n
  edges_ok : EdgesOk I.n I.edges

/-- The initialization words. -/
def words : List ℕ :=
  I.n :: edgeWords I.edges

/-- `G` after the first `t` deletions. -/
def Gt (σ : List ℕ) (t : ℕ) : Graph ℕ ℕ :=
  gAt (ofEdges I.n I.edges) (σ.map (fun e => [GUpdate.delE e])) t

/-- Valid operations: a present edge is deleted. -/
def Valid (σ : List ℕ) : Prop :=
  ∀ (t e : ℕ), σ[t]? = some e → e ∈ (I.Gt σ t).E

end TreeInput

/-- The clauses of Theorem 10.7 with the function `f` of the `o(1)` and the constant `C`. -/
structure TreeHolds (f : ℕ → ℝ) (C W : ℕ) (P : Program) (I : TreeInput) (σ : List ℕ) : Prop where
  runs : RunsThrough W P (treeProtocol.blocks I.words σ)
  /-- At all times: `k ≤ C·log₂(2+n)·log₂(2+L·n)` graphs, each a dominating tree embedding of `G`, and every pair `u, v` has an index `i`
  with `dist_{T_i}(u, v) ≤ C·log₂(2+n+m)^C·distG(u, v)·log₂(2 + L)`. -/
  log : ∀ t ≤ σ.length, ∃ s k, treeProtocol.state W P I.words σ t = some s ∧ s.k = some k ∧
    (k : ℝ) ≤ (C : ℝ) * lg (I.n : ℝ) * lg ((I.L : ℝ) * (I.n : ℝ)) ∧
    (∀ i < k, IsDominatingTreeEmbedding (I.Gt σ t) (s.trees i).g) ∧
    ∀ u ∈ (I.Gt σ t).V, ∀ v ∈ (I.Gt σ t).V, ∃ i < k,
      (((s.trees i).g.dist u v : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (polylog C I.n I.m * lg (I.L : ℝ)) * (((I.Gt σ t).dist u v : ℕ∞) : ℝ≥0∞)
  /-- The total update time `C·(m + n)^{1+f(m+n)}·log₂(2 + L)^C`. -/
  time : (treeProtocol.updateTime W P I.words σ : ℝ) ≤
    (C : ℝ) * ((I.m : ℝ) + (I.n : ℝ)) ^ (1 + f (I.m + I.n)) * lg (I.L : ℝ) ^ C

end DecrNbhdCover.Supplement


