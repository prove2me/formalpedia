-- Prove2me | Definitions.Def_WhitneyMatroid_Duality_IsDual
-- name    : WhitneyMatroid_Duality_IsDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:24:17.167506+00:00
-- url     : https://prove2.me/theorems/5b88f2fb-c42f-4c9e-a292-0da6727561d2
-- title:
--   Nullity and dual matroids (§2, §11, (11.1))
-- statement:
--   Let $M$ be a matroid on a finite set of elements, with rank function $r$. For a subset $N$ of $M$ write $\rho(N)$ for the number of elements of $N$. The **nullity** of $N$ is
--
--   $$
--   n(N) = \rho(N) - r(N).
--   $$
--
--   Let $M$ and $M'$ be matroids, each on a finite set of elements, and let $\sigma$ be a one-to-one correspondence between the elements of $M$ and those of $M'$. We say that $M'$ is a **dual of $M$ via $\sigma$** if for every subset $N$ of $M$, writing $N'$ for the complement in $M'$ of the set $\sigma(N)$ corresponding to $N$,
--
--   $$
--   r(N') = r(M') - n(N). \tag{11.1}
--   $$
--
--   $M'$ is a **dual** of $M$ if it is a dual of $M$ via some one-to-one correspondence $\sigma$.
--
--   The identity (11.1) is required for every subset $N$, including $N=\emptyset$ (where it is trivial) and $N=M$ (where $N'$ is empty). Duality is the abstract counterpart of planar graph duality and, as Theorem 28 shows, of orthogonal complementation of subspaces; Theorems 20–23 develop its basic properties.
--
--   **Formalization Note** A matroid is a Mathlib `Matroid` on a finite type whose ground set is the whole type (Whitney's matroid is its finite set of elements); this is part of the definition of `IsDualVia`. Ranks are Mathlib's `eRk`, which is finite on a finite type, converted to integers; the nullity and the identity (11.1) are computed in $\mathbb Z$, so no truncated subtraction occurs. The correspondence is a bijection `σ : α ≃ β` between the element types.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 510, §2 (nullity) and pp. 521–522, §11, (11.1)

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_nullity

namespace WhitneyMatroid.Duality

/-- Whitney §11, (11.1): `M′` is a dual of `M` via the one-to-one correspondence `σ` between their
elements. Both matroids live on finite types and have all of the type as ground set (Whitney's
matroid is its finite set of elements), and for every subset `N` of `M`, writing `N′` for the
complement in `M′` of the subset corresponding to `N`,
`r(N′) = r(M′) − n(N)`. Ranks are computed in `ℤ`. -/
def IsDualVia {α β : Type*} [Finite α] [Finite β] (M : Matroid α) (M' : Matroid β)
    (σ : α ≃ β) : Prop :=
  M.E = Set.univ ∧ M'.E = Set.univ ∧
    ∀ N : Set α,
      ((M'.eRk (Set.univ \ σ '' N)).toNat : ℤ) = ((M'.eRk Set.univ).toNat : ℤ) - WhitneyMatroid.Components.nullity M N

/-- Whitney §11: `M′` is a dual of `M` if there is some one-to-one correspondence between their
elements for which (11.1) holds. -/
def IsDual {α β : Type*} [Finite α] [Finite β] (M : Matroid α) (M' : Matroid β) : Prop :=
  ∃ σ : α ≃ β, IsDualVia M M' σ

end WhitneyMatroid.Duality


