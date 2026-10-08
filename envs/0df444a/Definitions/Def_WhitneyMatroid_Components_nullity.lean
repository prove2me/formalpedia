-- Prove2me | Definitions.Def_WhitneyMatroid_Components_nullity
-- name    : WhitneyMatroid_Components_nullity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:04:52.951444+00:00
-- url     : https://prove2.me/theorems/30386519-86cd-4a88-b07f-da15157bdfea
-- title:
--   Nullity $n(N) = \rho(N) - r(N)$
-- statement:
--   Let $M$ be a matroid with rank function $r$, and let $N$ be a finite set of its elements. Write $\rho(N)$ for the number of elements of $N$. The **nullity** of $N$ is
--
--   $$
--   n(N) = \rho(N) - r(N).
--   $$
--
--   It is zero exactly when $N$ is independent, and measures how far $N$ is from being independent. Whitney uses it in (10.2) and in Theorems 16 and 17.
--
--   **Formalization Note** The nullity is computed in $\mathbb Z$ from the number of elements of $N$ and the natural-number value of Mathlib's rank `M.eRk N`. It is intended for finite subsets of the ground set of a finite matroid, where both quantities are the true ones; every theorem of the mission that uses it assumes this.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 510, §2 (nullity) and p. 518, (10.2)

import Mathlib

namespace WhitneyMatroid.Components

/-- Whitney's nullity `n(N) = ρ(N) − r(N)` of a finite set `N` of elements: its number of
elements minus its rank, computed in `ℤ`. Meant for finite `N ⊆ M.E` of a finite matroid, where
both `N.ncard` and `(M.eRk N).toNat` are the true values. -/
noncomputable def nullity {α : Type*} (M : Matroid α) (N : Set α) : ℤ :=
  (N.ncard : ℤ) - ((M.eRk N).toNat : ℤ)

end WhitneyMatroid.Components


