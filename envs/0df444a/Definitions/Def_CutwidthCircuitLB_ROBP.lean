-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP
-- name    : CutwidthCircuitLB_ROBP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:26.939372+00:00
-- url     : https://prove2.me/theorems/6370290b-e3a9-4e03-8b3a-4148791547d8
-- title:
--   Read-once program (NROBP) on $n$ variables
-- statement:
--   A (nondeterministic) **read-once program** on the variables $x_1, \dots, x_n$ is a directed layered multigraph with pairwise disjoint vertex sets $V_0, \dots, V_\ell$, a distinguished **start** vertex in $V_0$ and a distinguished **accept** vertex in $V_\ell$. Edges go only from $V_{i-1}$ to $V_i$ for some $i \in \{1, \dots, \ell\}$; for each such $i$ these edges form the $i$-th **transition layer**. Every vertex has outdegree at most four. Each transition layer is either a **query layer**, tagged with a variable $x_j$ and with edges labeled $0$ or $1$, or a **guess layer**, whose edges are unlabeled. Every variable tags exactly one query layer. Parallel edges are permitted and counted with multiplicity. The **length** of the program is $\ell$.
--
--   Lemma 3.1 compiles small circuits into such programs, and Lemma 4.1 shows that programs computing a rectangle disperser need many edges.
--
--   **Formalization Note** Layer $V_i$ is $\{0, \dots, |V_i| - 1\}$, which makes the layers disjoint. The paper's transition layer $t+1$ is indexed by $t \in \{0, \dots, \ell - 1\}$; it is tagged by $x_j$ or marked as a guess layer. Its edges form a list of triples (source, target, label), so parallel edges count with multiplicity; the label of an edge in a guess layer is never read.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2, p.7

import Mathlib

namespace CutwidthCircuitLB

/-- A (nondeterministic) **read-once program** on the variables `x₁, …, xₙ` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3),
Definition 2.2, p.7): a directed layered multigraph with pairwise disjoint vertex layers
`V₀, …, V_ℓ`, a start vertex in `V₀` and an accept vertex in `V_ℓ`. Edges go only from `V_(i−1)` to
`V_i`, forming the `i`-th transition layer. Every vertex has outdegree at most four. Each
transition layer is a query layer, tagged with a variable `x_j` and with edges labeled `0` or
`1`, or a guess layer, with unlabeled edges. Every variable tags exactly one query layer. Parallel
edges are permitted and counted with multiplicity.

**Formalization Note** `len` is the length `ℓ`; the vertices of layer `i` are `Fin (layerSize i)`
(so the layers are disjoint). Transition layer `t + 1` of the paper is `t : Fin len`; it goes from
layer `t` to layer `t + 1`, it is a query layer tagged `x_j` iff `tag t = some j` and a guess layer
iff `tag t = none`. Its edges are a `List` of (source, target, label) triples, so parallel edges
count with multiplicity; the label of an edge in a guess layer is never read. -/
structure ROBP (n : ℕ) where
  /-- the length `ℓ` -/
  len : ℕ
  /-- `|V_i|` -/
  layerSize : Fin (len + 1) → ℕ
  /-- the start vertex, in `V₀` -/
  start : Fin (layerSize 0)
  /-- the accept vertex, in `V_ℓ` -/
  accept : Fin (layerSize (Fin.last len))
  /-- the variable tagging each transition layer (`none` for a guess layer) -/
  tag : Fin len → Option (Fin n)
  /-- the edges of each transition layer: (source, target, label), with multiplicity -/
  edges : (t : Fin len) → List (Fin (layerSize t.castSucc) × Fin (layerSize t.succ) × Bool)
  /-- every vertex has outdegree at most four -/
  outdeg_le : ∀ (t : Fin len) (u : Fin (layerSize t.castSucc)),
    (edges t).countP (fun e => e.1 = u) ≤ 4
  /-- every variable tags exactly one query layer -/
  tag_unique : ∀ j : Fin n, ∃! t : Fin len, tag t = some j

end CutwidthCircuitLB


