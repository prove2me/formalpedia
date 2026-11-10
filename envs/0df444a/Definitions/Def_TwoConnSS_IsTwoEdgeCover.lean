-- Prove2me | Definitions.Def_TwoConnSS_IsTwoEdgeCover
-- name    : TwoConnSS_IsTwoEdgeCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:34.261199+00:00
-- url     : https://prove2.me/theorems/3f606ccf-6a8b-4935-878e-6d4c7b5667f2
-- title:
--   2-edge-covers, triangle-free covers and weak 2-edge-covers
-- statement:
--   Let $G$ be a graph and $S \subseteq E(G)$.
--
--   1. $S$ is a **2-edge-cover** if every vertex has degree at least $2$ in $(V, S)$.
--   2. $S$ is **triangle-free** if no component of $(V,S)$ is a triangle. Triangles inside larger components are allowed: the restriction concerns components, not all cycles.
--   3. $S$ is a **weak 2-edge-cover** if every vertex has degree $0$ or at least $2$.
--
--   Every 2ECSS of a graph on at least four vertices is a triangle-free 2-edge-cover, which is why a minimum triangle-free 2-edge-cover is a lower bound for 2ECSS.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §6, p.25; Definition 8.5, p.33

import Mathlib
import Definitions.Def_TwoConnSS_blocks

namespace TwoConnSS

variable {V : Type*} [Fintype V]

/-- **2-edge-cover.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §6, p.25: "A 2-edge-cover is an
edge set in which every vertex has degree at least two." Here `S ⊆ E(G)`. -/
def IsTwoEdgeCover (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop :=
  (S : Set (Sym2 V)) ⊆ G.edgeSet ∧ ∀ v, 2 ≤ deg S v

/-- **Triangle-free cover.** §6, p.25: "A triangle-free cover or matching has no triangle
component … These restrictions concern components, not all cycles in the input graph." -/
def IsTriangleFree (S : Finset (Sym2 V)) : Prop :=
  ∀ C, ¬ IsCycleComp S C 3

/-- **Weak 2-edge-cover** (Definition 8.5, p.33): "a selected spanning subgraph S in which every
vertex has degree zero or degree at least two." Here `S ⊆ E(G)`. -/
def IsWeakCover (G : SimpleGraph V) (S : Finset (Sym2 V)) : Prop :=
  (S : Set (Sym2 V)) ⊆ G.edgeSet ∧ ∀ v, deg S v = 0 ∨ 2 ≤ deg S v

end TwoConnSS


