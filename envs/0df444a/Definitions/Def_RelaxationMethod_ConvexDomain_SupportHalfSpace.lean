-- Prove2me | Definitions.Def_RelaxationMethod_ConvexDomain_SupportHalfSpace
-- name    : RelaxationMethod_ConvexDomain_SupportHalfSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:46:10.930144+00:00
-- url     : https://prove2.me/theorems/82bf90c7-0335-46cb-b792-846dfe055c83
-- title:
--   The family $F$ of supporting half-spaces of a convex set (§9)
-- statement:
--   Let $A \subseteq E_n$. A set $H \subseteq E_n$ **belongs to the family $F$ of $A$** if it is a closed half-space
--   $$H = \{x \in E_n : \langle u, x\rangle \ge c\}, \qquad u \ne 0,\ c \in \mathbb{R},$$
--   such that $A \subseteq H$ and the bounding hyperplane $\{x : \langle u, x\rangle = c\}$ contains a point of $A$, i.e. it is a hyperplane of support of $A$.
--
--   For a closed convex set $A$, the intersection of all members of $F$ is $A$ itself; the reflexion process with respect to $A$ is the relaxation process with respect to this infinite family of half-spaces.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), p. 402, §9

import Mathlib

namespace RelaxationMethod.ConvexDomain

/-- §9, p. 402: the closed half-space `H` belongs to the family `F` of `A`: `H = {x | c ≤ ⟪u, x⟫}`
for some nonzero `u` and real `c`, `A ⊆ H`, and the bounding hyperplane `{x | ⟪u, x⟫ = c}` meets
`A` (it is a hyperplane of support of `A`). -/
def IsSupportHalfSpace {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (H : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ u : EuclideanSpace ℝ (Fin n), u ≠ 0 ∧ ∃ c : ℝ,
    H = {x | c ≤ inner ℝ u x} ∧ A ⊆ H ∧ ∃ a ∈ A, inner ℝ u a = c

end RelaxationMethod.ConvexDomain


