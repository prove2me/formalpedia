-- Prove2me | Definitions.Def_GarrettFA_IsInitTopology
-- name    : GarrettFA_IsInitTopology
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T19:28:06.721467+00:00
-- url     : https://prove2.me/theorems/e920f25b-64c1-4000-bdd4-0a1e87d0a940
-- title:
--   The finest locally convex topology $V_{\mathrm{init}}$
-- statement:
--   Let $V$ be a vector space over $\mathbb K=\mathbb R$ or $\mathbb C$ with a topological vector space topology. The topology of $V$ is **the topology of $V_{\rm init}$**, the locally convex colimit of the finite-dimensional subspaces of $V$, if:
--
--   1. $V$ is locally convex, and
--   2. every balanced convex set $U\subseteq V$ such that $U\cap W$ is a neighbourhood of $0$ in $W$ for every finite-dimensional subspace $W$ is a neighbourhood of $0$ in $V$.
--
--   In the notes, $V_{\rm init}$ is used to show that weak duals of most spaces are not complete: it carries the finest locally convex topology, and for it every linear functional is continuous.
--
--   **Formalization Note** The predicate describes the given topology of $V$; finite-dimensional subspaces carry the subspace topology, which for Hausdorff $V$ is their unique vector space topology. Existence of such a topology on every vector space is a separate theorem item of the mission.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 8, §5 (definition of $V_{\rm init}$ as the locally convex colimit of the finite-dimensional subspaces)

import Mathlib

namespace GarrettFA

open Topology

/-- Garrett, *Completeness and quasi-completeness*, §5: the topology of `V` is the topology of
`V_init`, the locally convex colimit of the finite-dimensional subspaces of `V`:
1. `V` is locally convex (real convexity, `V` being a real vector space by restriction of
   scalars);
2. every balanced convex subset `U ⊆ V` whose trace `U ∩ W` is a neighbourhood of `0` in `W`
   for every finite-dimensional subspace `W` is a neighbourhood of `0` in `V`.
Each `W` carries the subspace topology from `V` (for a Hausdorff topological vector space this
is the unique Hausdorff vector space topology on `W`). -/
structure IsInitTopology (𝕜 : Type*) (V : Type*) [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] : Prop where
  locallyConvex : LocallyConvexSpace ℝ V
  mem_nhds_of_balanced_convex : ∀ U : Set V, Balanced 𝕜 U → Convex ℝ U →
    (∀ W : Submodule 𝕜 V, FiniteDimensional 𝕜 W → {y : W | (y : V) ∈ U} ∈ 𝓝 (0 : W)) →
    U ∈ 𝓝 (0 : V)

end GarrettFA


