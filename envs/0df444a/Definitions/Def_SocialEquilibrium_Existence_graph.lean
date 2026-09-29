-- Prove2me | Definitions.Def_SocialEquilibrium_Existence_graph
-- name    : SocialEquilibrium_Existence_graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:37:56.465683+00:00
-- url     : https://prove2.me/theorems/e6d8a6b2-c7ad-450d-8cc2-ba377c067fa8
-- title:
--   Graph of a multi-valued function; semicontinuity
-- statement:
--   A **multi-valued function** $\varphi$ from a set $Z$ to a set $W$ associates with each $z\in Z$ a subset $\varphi(z)\subseteq W$. Its **graph** is
--   $$\operatorname{graph}\varphi=\{(z,w)\in Z\times W \mid w\in\varphi(z)\}.$$
--   When $Z$ and $W$ are topological spaces, $\varphi$ is **semicontinuous** if its graph is closed in $Z\times W$ (product topology).
--
--   Debreu uses the graph $G_\iota$ of each agent's constraint map $A_\iota$ and calls a multi-valued function semicontinuous when its graph is closed. In the fixed-point LEMMA, a *fixed point* of $\varphi: Z\to Z$ is a point $z^*$ with $z^*\in\varphi(z^*)$.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 888 (graph G_ι of A_ι) and p. 889 (graph of φ, semicontinuous)

import Mathlib

namespace SocialEquilibrium.Existence

/-- Debreu (1952), p. 888–889: the *graph* of a multi-valued function `φ`, which associates
with each `z ∈ Z` a subset `φ z ⊆ W`, is the set `{(z, w) | w ∈ φ z} ⊆ Z × W`. -/
def graph {Z W : Type*} (φ : Z → Set W) : Set (Z × W) :=
  {p | p.2 ∈ φ p.1}

/-- Debreu (1952), p. 889: a multi-valued function is *semicontinuous* if its graph is
closed. -/
def IsSemicontinuous {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    (φ : Z → Set W) : Prop :=
  IsClosed (graph φ)

end SocialEquilibrium.Existence


