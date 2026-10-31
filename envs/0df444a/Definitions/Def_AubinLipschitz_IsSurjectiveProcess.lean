-- Prove2me | Definitions.Def_AubinLipschitz_IsSurjectiveProcess
-- name    : AubinLipschitz_IsSurjectiveProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:04.9544+00:00
-- url     : https://prove2.me/theorems/56a2d1b8-9ed1-4a07-b75a-cd20ffc95e5e
-- title:
--   Surjective set-valued map
-- statement:
--   A set-valued map $G$ from $X$ to $Y$ is **surjective** when its image is all of $Y$:
--
--   $$
--   \forall v\in Y,\ \exists u\in X,\quad v\in G(u).
--   $$
--
--   This is the condition "$\operatorname{Im} CF(x_0,y_0)=Y$" of the Inverse Function Theorem.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Theorem 1, (2)ii, p.22

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §3, Theorem 1 (2)ii, p.22 ("Im CF(x₀, y₀) = Y"): a set-valued map `G : X ⇉ Y` is
*surjective* when every `v : Y` lies in `G(u)` for some `u`. -/
def IsSurjectiveProcess {X Y : Type*} (G : X → Set Y) : Prop :=
  ∀ v : Y, ∃ u : X, v ∈ G u

end AubinLipschitz


