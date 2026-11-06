-- Prove2me | Definitions.Def_ZeroOneExpansion_IsAdj
-- name    : ZeroOneExpansion_IsAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:12.16011+00:00
-- url     : https://prove2.me/theorems/c245e48d-58e3-4867-8a1b-f64b4e56e5ca
-- title:
--   Vertices and adjacency in the graph $G(P)$ of a convex set
-- statement:
--   A point $x$ is a **vertex** of $P$ when $\{x\}$ is a face of $P$, i.e. the set of maximizers on $P$ of some linear functional. An **edge** of $P$ is a one-dimensional face. Two vertices $u\neq v$ are **adjacent** in the graph $G(P)=(V(P),E(P))$ when they lie in a common face of $P$ whose affine hull is one-dimensional.
--
--   **Formalization Note** These are Mathlib's exposed faces, defined over an arbitrary real topological vector space so that they apply to the products $\prod_i\mathbb R^{d_i}$ of Fact 5 and to the factors $Q$, $\Delta$ of Lemma 8. On $\mathbb R^d$ they are the vertices and the adjacency of the published `Grunbaum2003.PolytopeVertex` and `Grunbaum2003.polytopeGraph`; the agreement is proved in the mission's verification file.
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §2.1, p.3, "vertex", "edge", "graph"

import Mathlib

set_option autoImplicit false

namespace ZeroOneExpansion

/-- `x` is a **vertex** of `P`: `{x}` is a face of `P`, i.e. the set of maximizers on `P` of some
linear functional (arXiv:2608.01870, §2.1, p.3: "A zero-dimensional face is called a vertex").

**Formalization Note** This is Mathlib's `IsExposed ℝ P {x}` over an arbitrary real topological
vector space; on `Fin d → ℝ` it is the defining predicate of the published
`Grunbaum2003.PolytopeVertex`. The general ambient space is needed for the products `∏ ℝ^{d_i}` of
Fact 5. On finite-dimensional spaces every linear functional is continuous. -/
def IsVertexOf {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (P : Set E) (x : E) : Prop :=
  IsExposed ℝ P {x}

/-- Two vertices `u, v` of `P` are **adjacent** in the graph `G(P)`: they are distinct and lie in a
common one-dimensional face of `P` (arXiv:2608.01870, §2.1, p.3: "A one-dimensional face is a closed
segment with two vertices as endpoints and is called an edge. We write V(P) for the vertex set and
E(P) for the set of unordered endpoint pairs of the edges").

**Formalization Note** The same relation as the published `Grunbaum2003.polytopeGraph` (distinct
vertices in a common exposed face whose affine hull has dimension one), restated over an arbitrary
real topological vector space so that it applies to the factors and the product in Fact 5 and to the
factors `Q = [0,1]^2`, `∆` in Lemma 8. Its agreement with `Grunbaum2003.polytopeGraph` on
`Fin d → ℝ` is proved in `Solutions/verification`. -/
def IsAdj {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (P : Set E) (u v : E) : Prop :=
  u ≠ v ∧ IsVertexOf P u ∧ IsVertexOf P v ∧
    ∃ F : Set E, IsExposed ℝ P F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 1 ∧
      u ∈ F ∧ v ∈ F

end ZeroOneExpansion


