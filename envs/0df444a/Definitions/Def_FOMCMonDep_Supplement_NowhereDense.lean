-- Prove2me | Definitions.Def_FOMCMonDep_Supplement_NowhereDense
-- name    : FOMCMonDep_Supplement_NowhereDense
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:17:43.352203+00:00
-- url     : https://prove2.me/theorems/96f1ef1b-83f5-45a9-8a02-e8abe2d577db
-- title:
--   Nowhere dense graph classes (excluded shallow topological cliques)
-- statement:
--   For a graph $G$ and $r,t\in\mathbb N$, the clique $K_t$ is a **topological depth-$r$ minor** of $G$ if $G$ contains a $(\le 2r)$-subdivision of $K_t$ as a subgraph. That is, there are $t$ distinct **branch vertices** $v_1,\dots,v_t$ and, for every pair $i<j$, a path in $G$ from $v_i$ to $v_j$ of length at most $2r+1$. No internal vertex of these paths is a branch vertex, and the paths of two distinct pairs share no internal vertex.
--
--   A graph class $\mathcal C$ is **nowhere dense** if for every $r\in\mathbb N$ there is $t\in\mathbb N$ such that $K_t$ is a topological depth-$r$ minor of no graph in $\mathcal C$.
--
--   This is the sparsity notion of Nešetřil and Ossona de Mendez and of Grohe, Kreutzer and Siebertz, used in Theorem 4.8. Every nowhere dense class is monadically dependent.
--
--   **Formalization Note** A graph class is the published `MonDepMW.GraphClass`: a set of graphs on each vertex set $\{0,\dots,n-1\}$. The topological-minor variant is used. The variants with $(\le r)$-subdivisions or with shallow minors define the same classes, because $r$ ranges over all of $\mathbb N$. No closure condition (hereditary, monotone) is added. The helper `HasShallowTopClique G r t` says that $K_t$ is a topological depth-$r$ minor of $G$.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 4.8, p.15 (PDF 17), and App. C, p.63 (PDF 65), using the notion of [NO11] (Nešetřil, Ossona de Mendez, On nowhere dense graphs, European J. Combin. 32 (2011)) and [GKS17] (Grohe, Kreutzer, Siebertz, Deciding first-order properties of nowhere dense graphs, J. ACM 64(3), 2017)

import Mathlib
import Definitions.Def_MonDepMW_MonadicallyDependent

set_option autoImplicit false

namespace FOMCMonDep.Supplement

/-- The internal vertices of a walk: its support without the first and the last vertex. -/
def internalVerts {V : Type} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : List V :=
  p.support.tail.dropLast

/-- **`K_t` is a topological depth-`r` minor of `G`** (a `≤ 2r`-subdivision of the clique `K_t` is a subgraph of `G`):
there are `t` distinct branch vertices `f 0, …, f (t − 1)` and, for every pair `i < j`, a path in `G` from `f i` to
`f j` of length at most `2r + 1` whose internal vertices are not branch vertices, the paths of distinct pairs having no
internal vertex in common. Nešetřil, Ossona de Mendez, *On nowhere dense graphs*, European J. Combin. 32 (2011);
Grohe, Kreutzer, Siebertz, *Deciding first-order properties of nowhere dense graphs*, J. ACM 64(3) (2017). -/
def HasShallowTopClique {n : ℕ} (G : SimpleGraph (Fin n)) (r t : ℕ) : Prop :=
  ∃ (f : Fin t ↪ Fin n) (p : ∀ i j : Fin t, i < j → G.Walk (f i) (f j)),
    (∀ i j (h : i < j), (p i j h).IsPath ∧ (p i j h).length ≤ 2 * r + 1 ∧
        ∀ x ∈ internalVerts (p i j h), x ∉ Set.range f) ∧
    ∀ i j i' j' (h : i < j) (h' : i' < j'), (i, j) ≠ (i', j') →
      ∀ x ∈ internalVerts (p i j h), x ∉ internalVerts (p i' j' h')

/-- **Nowhere dense graph classes.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically
Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), Theorem 4.8, p.15 (PDF 17), and
App. C, p.63 (PDF 65), which use the notion of [NO11; GKS17] without restating it. A graph class `𝒞` is nowhere dense
if for every `r ∈ ℕ` there is `t ∈ ℕ` such that `K_t` is not a topological depth-`r` minor of any graph of `𝒞`
(no `≤ 2r`-subdivision of `K_t` is a subgraph).

**Formalization Note.** The class is the published `MonDepMW.GraphClass` (its members on each vertex set `Fin n`).
The variant with topological minors is used; the variants with `≤ r`-subdivisions or with shallow minors define the same
classes, since `r` ranges over all of `ℕ`. `t` is chosen after `r` and uniformly over all graphs of the class. No
closure (hereditary, monotone) condition is added. -/
def NowhereDense (𝒞 : MonDepMW.GraphClass) : Prop :=
  ∀ r : ℕ, ∃ t : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ¬ HasShallowTopClique G r t

end FOMCMonDep.Supplement


