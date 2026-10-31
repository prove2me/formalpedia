-- Prove2me | Definitions.Def_MalleableSched_Pseudoforest
-- name    : MalleableSched_Pseudoforest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:18.379427+00:00
-- url     : https://prove2.me/theorems/10a39c19-7a8c-4108-be4f-97545b84b565
-- title:
--   Pseudoforests and orientations with in-degree at most one
-- statement:
--   A finite graph $G$ is a **pseudoforest** if every connected component is a tree or contains at most one cycle; equivalently, every set $s$ of vertices spans at most $|s|$ edges.
--
--   An **orientation** of $G$ directs every edge $\{u,v\}$ either $u\to v$ or $v\to u$. It has **in-degree at most one** if every vertex is the head of at most one directed edge.
--
--   These notions enter through the rounding argument of Lenstra, Shmoys and Tardos, which the paper uses in Appendix A.3 to round an extreme point of its LP.
--
--   **Formalization Note** A graph is a Mathlib `SimpleGraph` on a finite vertex type. The pseudoforest condition is the counting form: for every finite vertex set $s$, the number of ordered adjacent pairs inside $s$ is at most $2|s|$ (each edge is counted twice). An orientation is a relation $D$ with $D(u,v)\iff\neg D(v,u)$ for adjacent $u,v$.
-- source:
--   Fotakis, Matuschke & Papadigenopoulos, Assigning and Scheduling Generalized Malleable Jobs, arXiv:2111.06225v2, Appendix A.3, p.27

import Mathlib

namespace MalleableSched

/-- **Pseudoforest (finite simple graph).** Fotakis, Matuschke & Papadigenopoulos,
arXiv:2111.06225v2, Appendix A.3, p.27: "G is a pseudoforest, in the sense that all its connected
components are either trees, or contain at most one cycle."

**Formalization Note.** Counting form: every finite vertex set `s` spans at most `|s|` edges.
Edges are counted as ordered adjacent pairs inside `s`, each edge twice, hence the bound
`2 * s.card`. A finite graph has this property iff every connected component has at most as many
edges as vertices, i.e. is a tree or contains at most one cycle. -/
def IsPseudoforestGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  ∀ s : Finset V, ((s ×ˢ s).filter (fun p => G.Adj p.1 p.2)).card ≤ 2 * s.card

/-- **Orientation with every in-degree at most one.** arXiv:2111.06225v2, Appendix A.3, p.27:
"the edges of G (and of any pseudoforest) can be oriented in a way that each node has an in-degree
of at most one."

**Formalization Note.** An orientation is a relation `D` (`D u v`: the edge `{u, v}` is directed
`u → v`) such that each edge gets exactly one direction (`D u v ↔ ¬ D v u` for adjacent `u, v`);
its values on non-edges are irrelevant. In-degree at most one: for every `v`, at most one
neighbour `u` has `D u v`. -/
def IsOrientationInDegLeOne {V : Type*} (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  (∀ u v, G.Adj u v → (D u v ↔ ¬ D v u)) ∧ ∀ v, {u | G.Adj u v ∧ D u v}.Subsingleton

end MalleableSched


