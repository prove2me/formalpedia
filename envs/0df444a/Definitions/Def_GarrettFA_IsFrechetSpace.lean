-- Prove2me | Definitions.Def_GarrettFA_IsFrechetSpace
-- name    : GarrettFA_IsFrechetSpace
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T19:26:10.324984+00:00
-- url     : https://prove2.me/theorems/5548dc3a-b189-4877-b843-e5aa01785f42
-- title:
--   Fréchet space
-- statement:
--   A topological vector space $X$ over $\mathbb K=\mathbb R$ or $\mathbb C$ is a **Fréchet space** if it is
--
--   1. locally convex,
--   2. metrizable, and
--   3. complete for its canonical uniform structure.
--
--   Banach and Hilbert spaces are Fréchet spaces.
--
--   **Formalization Note** Local convexity is real local convexity. Completeness refers to the uniform structure on $X$, which the theorems using this predicate require to be the canonical translation-invariant uniformity.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 1 and §1.3 (Fréchet spaces as locally convex, metrizable, complete spaces)

import Mathlib

namespace GarrettFA

/-- A Fréchet space: a locally convex topological vector space whose topology is metrizable
and which is complete (for its uniform structure, which in applications is the canonical
uniformity of the topological vector space). -/
def IsFrechetSpace (𝕜 : Type*) (X : Type*) [RCLike 𝕜] [AddCommGroup X] [Module 𝕜 X]
    [Module ℝ X] [IsScalarTower ℝ 𝕜 X] [UniformSpace X] : Prop :=
  LocallyConvexSpace ℝ X ∧ TopologicalSpace.MetrizableSpace X ∧ CompleteSpace X

end GarrettFA


