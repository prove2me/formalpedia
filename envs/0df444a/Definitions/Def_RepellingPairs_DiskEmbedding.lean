-- Prove2me | Definitions.Def_RepellingPairs_DiskEmbedding
-- name    : RepellingPairs_DiskEmbedding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:20.995362+00:00
-- url     : https://prove2.me/theorems/abbca988-b519-4db3-b25d-67e3e1f0a64b
-- title:
--   Embedding of a multigraph in the closed unit disk
-- statement:
--   An **embedding** of a multigraph in the closed unit disk of $\mathbb C$ places the vertices at distinct points of the disk and each edge on a continuous arc $[0,1]\to$ disk joining the positions of its two ends. An arc is injective, except that the two endpoints of a loop's arc agree. The interior of an arc contains no vertex, and two distinct arcs meet only at arc endpoints.
--
--   This is the topological meaning of "embedded in a closed disk" in the definition of an Okamura-Seymour instance.
--
--   **Formalization Note** Any closed disk is homeomorphic to the unit disk. Vertices and arc interiors may lie on the boundary circle, as the paper allows.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, p.5

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- An embedding of a multigraph in the closed unit disk of `ℂ` ("embedded in a closed disk", §2,
p.5). Vertices are distinct points of the disk; each edge is a continuous arc in the disk joining the
points of its two ends, injective except that the two endpoints of a loop's arc agree; the interior
of an arc contains no vertex; two distinct arcs meet only at arc endpoints.
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §2, p.5.

**Formalization Note.** Any closed disk is homeomorphic to the unit disk. Nothing keeps vertices or arc
interiors off the boundary circle: "Other graph vertices may also lie on the boundary". -/
structure DiskEmbedding {V : Type u} {E : Type v} (G : Multigraph V E) where
  /-- The position of a vertex. -/
  pos : V → ℂ
  /-- The arc of an edge, parametrized by `[0, 1]`. -/
  arc : E → ℝ → ℂ
  pos_injective : Function.Injective pos
  pos_mem_disk : ∀ v, ‖pos v‖ ≤ 1
  arc_continuousOn : ∀ e, ContinuousOn (arc e) (Set.Icc 0 1)
  arc_mem_disk : ∀ e, ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖arc e s‖ ≤ 1
  arc_ends : ∀ e, ∃ u v, G.ends e = s(u, v) ∧ arc e 0 = pos u ∧ arc e 1 = pos v
  arc_injOn : ∀ e, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1, arc e s = arc e r →
    s = r ∨ ((s = 0 ∨ s = 1) ∧ (r = 0 ∨ r = 1))
  arc_interior_avoids_pos : ∀ e, ∀ s ∈ Set.Ioo (0 : ℝ) 1, ∀ w, arc e s ≠ pos w
  arc_disjoint : ∀ e f, e ≠ f → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
    arc e s = arc f r → (s = 0 ∨ s = 1) ∧ (r = 0 ∨ r = 1)

end RepellingPairs


