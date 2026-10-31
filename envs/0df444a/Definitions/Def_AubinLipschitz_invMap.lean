-- Prove2me | Definitions.Def_AubinLipschitz_invMap
-- name    : AubinLipschitz_invMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:07.357991+00:00
-- url     : https://prove2.me/theorems/8afde918-e11b-49aa-9f43-7a218153f490
-- title:
--   The inverse of a set-valued map
-- statement:
--   The **inverse** of a set-valued map $F$ from $X$ to $Y$ is the set-valued map $F^{-1}$ from $Y$ to $X$ given by
--
--   $$
--   F^{-1}(y)=\{x\in X\mid y\in F(x)\}.
--   $$
--
--   Every set-valued map has an inverse, and $(F^{-1})^{-1}=F$. The stability questions of the mission are questions about the inverse of the map sending a solution to the parameters it solves for.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Definition 1, p.22

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, p.22: the inverse `F⁻¹ : Y ⇉ X` of a set-valued map, `F⁻¹(y) = {x | y ∈ F(x)}`. -/
def invMap {X Y : Type*} (F : X → Set Y) : Y → Set X :=
  fun y => {x | y ∈ F x}

end AubinLipschitz


