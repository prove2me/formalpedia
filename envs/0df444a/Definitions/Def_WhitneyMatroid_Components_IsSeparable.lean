-- Prove2me | Definitions.Def_WhitneyMatroid_Components_IsSeparable
-- name    : WhitneyMatroid_Components_IsSeparable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:45.90759+00:00
-- url     : https://prove2.me/theorems/9ef37495-6248-4586-93be-0e9a8dd35540
-- title:
--   Separable and non-separable submatroids (§10, (10.1))
-- statement:
--   Let $M$ be a matroid on a ground set $E$ with rank function $r$, and let $X\subseteq E$. Whitney regards $X$ itself as a matroid (a **submatroid** of $M$), whose rank function is the restriction of $r$ to the subsets of $X$.
--
--   The submatroid $X$ is **separable** if its elements can be divided into two groups $X_1$ and $X_2$, each containing at least one element and having no element in common, such that
--
--   $$
--   r(X) = r(X_1) + r(X_2).
--   $$
--
--   The submatroid $X$ is **non-separable** if $X\subseteq E$ and $X$ is not separable.
--
--   By subadditivity of the rank, $r(X)\le r(X_1)+r(X_2)$ always holds for $X=X_1+X_2$; separability asks for equality, i.e. the two groups contribute independently to the rank. Every single element forms a non-separable matroid, since it cannot be divided into two nonempty groups. Separability is the basis of Whitney's notion of component, and of every result of §10.
--
--   **Formalization Note** Ranks are Mathlib's extended-natural rank `M.eRk`; on the finite matroids of this mission all ranks are finite, so the equation is an ordinary equation of natural numbers. The requirement that each group contain at least one element is part of the definition: without it every set would be separable. Under this definition the empty set is non-separable (it admits no division into two nonempty groups); components are therefore required to be nonempty separately.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 518, §10, (10.1)

import Mathlib

namespace WhitneyMatroid.Components

/-- Whitney §10, (10.1): the submatroid `X` of `M` (the set `X` with the rank `M.eRk` restricted to
its subsets) is *separable* if `X` can be divided into two disjoint groups `X₁`, `X₂`, each
containing at least one element, with `r(X) = r(X₁) + r(X₂)`. -/
def IsSeparable {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  ∃ X₁ X₂ : Set α, X₁.Nonempty ∧ X₂.Nonempty ∧ Disjoint X₁ X₂ ∧ X₁ ∪ X₂ = X ∧
    M.eRk X = M.eRk X₁ + M.eRk X₂

/-- Whitney §10: a submatroid `X ⊆ M.E` is *non-separable* if it is not separable. -/
def IsNonSeparable {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  X ⊆ M.E ∧ ¬ IsSeparable M X

end WhitneyMatroid.Components


