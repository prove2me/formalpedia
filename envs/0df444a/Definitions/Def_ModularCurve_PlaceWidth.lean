-- Prove2me | Definitions.Def_ModularCurve_PlaceWidth
-- name    : ModularCurve_PlaceWidth
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/cdcccf1e-cb04-51f1-a46c-5d7cd7124fad
-- title:
--   Ramification over the j-line and place width
-- statement:
--   Two natural-number invariants are attached to a place of the level-$N$ geometric modular function field over a field $K$, for $N$ a nonzero natural number. Recall that $K$-places of $F$ in this development are valuation subrings of $F$ containing the image of $K$, proper and with principal ideals, with `ord` the associated normalised integer valuation and `evalAt` the $K$-valued evaluation at the place; `jGeomGen K N` is the distinguished generator of `modularFunctionFieldC K N` given by the $q$-expansion of $j$.
--
--   First, `placeRamificationJ N w` is defined as the nonnegative truncation (`Int.toNat`) of $w\bigl(\tilde\jmath - a\bigr)$, where $\tilde\jmath =$ `jGeomGen K N` and $a = w.\mathrm{evalAt}(\tilde\jmath) \in K$ is the value of $\tilde\jmath$ at $w$, viewed in the function field through the structure map of $K$. Since $j - a$ is a uniformiser of the $j$-line at the point $j = a$, this is the ramification index of $w$ over that point whenever $w$ is a rational place lying in the affine locus where $\tilde\jmath$ and $\tilde\jmath_N$ are integral; for other places the truncation returns a value with no such interpretation.
--
--   Second, `placeWidth N w` is the natural-number quotient
--   $$\mathrm{jWidth}\bigl(w.\mathrm{evalAt}(\tilde\jmath)\bigr) \big/ \mathrm{placeRamificationJ}\,N\,w,$$
--   where `jWidth j` is the table $3$ if $j = 0$, $2$ if $j = 1728$, and $1$ otherwise. The division is Lean's truncating division on $\mathbb{N}$, so exactness of the quotient and positivity of the result are not part of the definition but must be proved separately; both definitions are total functions of the place, with no hypothesis of rationality, of affineness, or on an auxiliary characteristic.
--
--   **Relation to Mathlib.** Mathlib has no modular function fields or places-of-a-curve in this sense; both definitions are the project's own, built on its `Place` structure (valuation subring with `ord` and `evalAt`) and on `jWidth`.
--
--   **Where it is used.** These invariants record, at a place of the level-$N$ modular function field, the ramification of the forgetful map to the $j$-line and the width of the corresponding crossing: in characteristic $q$ with $q \nmid N$, at a supersingular place `placeWidth N w` is intended as the width of the associated node of the special fibre at $q$ of $X_0(Nq)$, data entering the analysis of the character group of the toric part of the Jacobian used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_PlaceWidth.lean

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

def placeRamificationJ {K : Type*} [Field K] (N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) : ℕ :=
  (w.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N)
    (w.evalAt (jGeomGen K N)))).toNat

def placeWidth {K : Type*} [Field K] [DecidableEq K] (N : ℕ) [NeZero N]
    (w : Place K (modularFunctionFieldC K N)) : ℕ :=
  jWidth (w.evalAt (jGeomGen K N)) / placeRamificationJ N w

end ModularCurve

end


