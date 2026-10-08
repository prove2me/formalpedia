-- Prove2me | Definitions.Def_DualityStability_WeakDuality_TopPairing
-- name    : DualityStability_WeakDuality_TopPairing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:38:44.564514+00:00
-- url     : https://prove2.me/theorems/12dee24d-67ad-4c79-ab4f-44d08b9e6fbd
-- title:
--   Topologically paired real vector spaces, §2, p. 169
-- statement:
--   Let $E$ and $E^*$ be real vector spaces, each carrying a locally convex Hausdorff topology that makes it a topological vector space, and let $\langle\cdot,\cdot\rangle : E\times E^*\to\mathbb R$ be a bilinear form. The pair $(E,E^*)$ is **topologically paired** when the topologies are compatible with the duality:
--
--   1. for each $x^*\in E^*$ the map $x\mapsto\langle x,x^*\rangle$ is continuous on $E$, and for each $x\in E$ the map $x^*\mapsto\langle x,x^*\rangle$ is continuous on $E^*$;
--   2. every continuous linear functional $\varphi$ on $E$ has the form $\varphi(x)=\langle x,x^*\rangle$ for exactly one $x^*\in E^*$;
--   3. every continuous linear functional $\psi$ on $E^*$ has the form $\psi(x^*)=\langle x,x^*\rangle$ for exactly one $x\in E$.
--
--   So the elements of each space are identified with the continuous linear functionals on the other. Standard instances are $E=E^*=\mathbb R^n$ with the dot product, and a normed space with its dual under the weak and weak-\* topologies. The pair $(E,E^*)$ and the pair $(F,F^*)$ of the convex programs in this mission are both of this kind.
--
--   **Formalization Note** The pairing is a bilinear map `E →ₗ[ℝ] E' →ₗ[ℝ] ℝ`. No norm, inner product, or specific dual-space construction is chosen; the compatibility of the topologies is recorded by the separate continuity and the two existence-and-uniqueness clauses.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 169, §2 (topologically paired spaces)

import Mathlib

namespace DualityStability.WeakDuality

/-- Topologically paired real vector spaces (Rockafellar 1967, §2, p. 169): `E` and `E'` are
locally convex Hausdorff real topological vector spaces in duality under the bilinear form
`pair`, and the topologies are compatible with the duality: the pairing is continuous in each
variable, and every continuous linear functional on either space is the pairing with a unique
element of the other space. -/
structure TopPairing (E E' : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
    [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E']
    [LocallyConvexSpace ℝ E'] [T2Space E'] where
  /-- The bilinear form `⟨x, x'⟩`. -/
  pair : E →ₗ[ℝ] E' →ₗ[ℝ] ℝ
  continuous_left : ∀ y : E', Continuous (fun x : E => pair x y)
  continuous_right : ∀ x : E, Continuous (fun y : E' => pair x y)
  /-- Every continuous linear functional on `E` is `⟨·, y⟩` for a unique `y : E'`. -/
  represents_left : ∀ φ : E →L[ℝ] ℝ, ∃! y : E', ∀ x : E, pair x y = φ x
  /-- Every continuous linear functional on `E'` is `⟨x, ·⟩` for a unique `x : E`. -/
  represents_right : ∀ φ : E' →L[ℝ] ℝ, ∃! x : E, ∀ y : E', pair x y = φ y

end DualityStability.WeakDuality


