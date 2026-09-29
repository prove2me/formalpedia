-- Prove2me | Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA
-- name    : ChatterjeeSamuelson_LinkedODE_ClassA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:45:53.63419+00:00
-- url     : https://prove2.me/theorems/150290dd-ddf1-47d9-a690-379e1afd4b19
-- title:
--   Class $A$ offer strategies (bounded, strictly increasing and differentiable except at the offer bounds)
-- statement:
--   Chatterjee and Samuelson restrict attention to the family $A$ of equilibria in which "each offer strategy is bounded above and below and is strictly increasing and differentiable except possibly at these offer bounds".
--
--   For an offer strategy $S$ on the value interval $[\underline v, \bar v]$, write $m = \inf S([\underline v, \bar v])$ and $M = \sup S([\underline v, \bar v])$ for its lowest and highest offers. $S$ is of **class $A$** on $[\underline v, \bar v]$ if
--
--   1. $S([\underline v, \bar v])$ is bounded above and below;
--   2. $S$ is nondecreasing on $[\underline v, \bar v]$;
--   3. whenever two different values $u \ne w$ in $[\underline v, \bar v]$ receive the same offer $S(u) = S(w)$, that offer is $m$ or $M$;
--   4. $S$ is differentiable at every $v \in (\underline v, \bar v)$ with $m < S(v) < M$.
--
--   An equilibrium $(S, B)$ is a class $A$ equilibrium when both strategies are of class $A$ on their value intervals.
--
--   **Formalization Note** Clause 2 is a reading of "strictly increasing … except possibly at these offer bounds": it excludes a strategy that jumps from its upper bound back to its lower bound. Differentiability is required at interior values only, which can only enlarge the class.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), p. 840 [PDF 6], §2, definition of the family A of equilibria

import Mathlib

open Set

namespace ChatterjeeSamuelson.LinkedODE

/-- The class `A` regularity condition on an offer strategy (Chatterjee & Samuelson,
*Bargaining under Incomplete Information*, Oper. Res. 31(5) 1983, §2, p. 840 [PDF 6],
unnumbered text: "We shall consider the family A of equilibria for which the following
assumption is met: Each offer strategy is bounded above and below and is strictly
increasing and differentiable except possibly at these offer bounds.").

`ClassA S lo hi`, for a strategy `S` on the value interval `[lo, hi]` with lowest offer
`m = inf S([lo, hi])` and highest offer `M = sup S([lo, hi])`, says:
1. `S([lo, hi])` is bounded above and below;
2. `S` is monotone (nondecreasing) on `[lo, hi]`;
3. two different values with the same offer have that offer equal to `m` or `M`
   (so `S` is strictly increasing except where it sits at an offer bound);
4. `S` is differentiable at every interior value `v ∈ (lo, hi)` with `m < S v < M`.

*Formalization Note.* Clause 2 is a reading of "strictly increasing … except possibly at
these offer bounds": it excludes a strategy that is strictly increasing between its flat
pieces but jumps from the upper bound back down to the lower one. Differentiability is
required at interior values only (at `lo`, `hi` a derivative would be one-sided); this
makes the class larger, never smaller. `sInf`/`sSup` are taken of a bounded set
(clause 1), nonempty whenever `lo ≤ hi`. -/
def ClassA (S : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  BddAbove (S '' Icc lo hi) ∧ BddBelow (S '' Icc lo hi) ∧ MonotoneOn S (Icc lo hi) ∧
    (∀ u ∈ Icc lo hi, ∀ w ∈ Icc lo hi, u ≠ w → S u = S w →
      S u = sInf (S '' Icc lo hi) ∨ S u = sSup (S '' Icc lo hi)) ∧
    (∀ v ∈ Ioo lo hi, sInf (S '' Icc lo hi) < S v → S v < sSup (S '' Icc lo hi) →
      DifferentiableAt ℝ S v)

end ChatterjeeSamuelson.LinkedODE


