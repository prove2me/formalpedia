-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
-- name    : AlgebraicGeometry_ModulesLocallyFreeOfRank
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/e4168554-0198-568f-b1ee-bea4721ab357
-- title:
--   Locally free sheaves of modules of fixed rank
-- statement:
--   For a scheme $X$ this module introduces the predicate [`AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank n M`](../def/AlgebraicGeometry_ModulesLocallyFreeOfRank.html#L13), for a natural number $n$ and an object $M$ of `X.Modules`, the category of sheaves of $\mathcal{O}_X$-modules on $X$. It is a `Prop`-valued structure with a single field, `exists_trivialization`, asserting: for every point $x$ of $X$ there is an open subset $U$ of $X$ with $x \in U$ such that the image of $M$ under the inverse-image functor `Modules.pullback U.ι` along the open immersion $U \hookrightarrow X$ admits an isomorphism, in the category of sheaves of $\mathcal{O}_U$-modules, to the free sheaf of modules `SheafOfModules.free` on the index type `ULift (Fin n)`. Thus the condition is that $M$ restricted to a neighbourhood of each point is isomorphic to $\mathcal{O}_U^{\oplus n}$, the free module on $n$ generators, the restriction being taken in the form of the pullback along the open immersion rather than via the restriction functor.
--
--   Two points of shape are worth recording. First, the isomorphism is required only to exist: the field asserts `Nonempty` of the type of isomorphisms, so no chosen trivialisation is carried as data and the whole structure is a proposition. Second, the rank $n$ is a single natural number, fixed for all of $X$; a module whose local ranks vary from one connected component to another satisfies the predicate for no $n$. The case $n = 1$ is the condition that $M$ be invertible, the free module on a one-element index type being the structure sheaf.
--
--   **Relation to Mathlib.** Built from Mathlib's category `Scheme.Modules`, its inverse-image functor `Modules.pullback` and the free sheaf `SheafOfModules.free`; the predicate packaging local freeness of constant rank $n$ is the project's own.
--
--   **Where it is used.** The predicate is used throughout the algebro-geometric part of the development, where sheaves of modules on schemes are handled: with $n = 1$ it is the invertibility condition underlying the relative Picard functor, and for general $n$ it is the rank condition imposed on vector bundles occurring there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesLocallyFreeOfRank.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

structure IsLocallyFreeOfRank (n : ℕ) (M : X.Modules) : Prop where
  exists_trivialization : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((Modules.pullback U.ι).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n)))

end AlgebraicGeometry.Scheme.Modules


