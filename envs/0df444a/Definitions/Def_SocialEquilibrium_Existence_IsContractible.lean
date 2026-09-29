-- Prove2me | Definitions.Def_SocialEquilibrium_Existence_IsContractible
-- name    : SocialEquilibrium_Existence_IsContractible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:37:34.406231+00:00
-- url     : https://prove2.me/theorems/cf52a775-8418-4da9-80ff-9357f542d0f1
-- title:
--   Deformable into a point; contractible set
-- statement:
--   Let $I=[0,1]$ and let $Z$ be a subset of a topological space. The set $Z$ is **deformable into the point** $z^0\in Z$ if there is a continuous map (a *deformation*)
--   $$H: I\times Z\to Z,\qquad H(0,z)=z,\quad H(1,z)=z^0\quad\text{for all } z\in Z,$$
--   where $I\times Z$ carries the product topology and $Z$ the subspace topology. A nonempty set $Z$ is **contractible** if it is deformable into some point $z^0\in Z$.
--
--   A contractible set is nonempty, since it contains the point $z^0$. Contractibility replaces convexity in Debreu's existence theorem: the action sets and the sets of constrained best responses are required to be contractible, not convex.
--
--   **Formalization Note** The point $z^0$ is an element of the subtype $Z$, which carries the nonemptiness that the paper's definition ("A nonempty set $Z$ …") requires. $I$ is Mathlib's `unitInterval`.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 888, §1 Topological Concepts (definition of contractible)

import Mathlib

namespace SocialEquilibrium.Existence

open unitInterval

/-- Debreu (1952), §1, p. 888: a set `Z` is *deformable into the point* `z₀ ∈ Z` if there is a
continuous map (a *deformation*) `H : I × Z → Z`, `I = [0, 1]`, with `H(0, z) = z` and
`H(1, z) = z₀` for all `z ∈ Z`. -/
def IsDeformableInto {Y : Type*} [TopologicalSpace Y] (Z : Set Y) (z₀ : Z) : Prop :=
  ∃ H : C(I × Z, Z), (∀ z : Z, H (0, z) = z) ∧ ∀ z : Z, H (1, z) = z₀

/-- Debreu (1952), §1, p. 888: a nonempty set `Z` is *contractible* if it is deformable into
some point `z₀ ∈ Z`. Nonemptiness is carried by the point `z₀ ∈ Z`. -/
def IsContractible {Y : Type*} [TopologicalSpace Y] (Z : Set Y) : Prop :=
  ∃ z₀ : Z, IsDeformableInto Z z₀

end SocialEquilibrium.Existence


