-- Prove2me | Definitions.Def_AubinLipschitz_graphOf
-- name    : AubinLipschitz_graphOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:02.361816+00:00
-- url     : https://prove2.me/theorems/009fa527-c801-4412-ace4-71460e04888e
-- title:
--   The graph of a set-valued map
-- statement:
--   A set-valued map $F$ from $X$ to $Y$ assigns to each $x\in X$ a subset $F(x)\subset Y$. Its **graph** is
--
--   $$
--   \operatorname{graph}(F)=\{(x,y)\in X\times Y \mid y\in F(x)\}.
--   $$
--
--   All derivatives of set-valued maps in this mission are defined through tangent cones to the graph.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, p.13

import Mathlib

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §2, p.13: the graph of a set-valued map `F : X ⇉ Y`, encoded as `F : X → Set Y`. -/
def graphOf {X Y : Type*} (F : X → Set Y) : Set (X × Y) :=
  {z | z.2 ∈ F z.1}

end AubinLipschitz


