-- Prove2me | Definitions.Def_VectorSpaceOpt_is_nbv_open
-- name    : VectorSpaceOpt_is_nbv_open
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-27T03:14:06.071581+00:00
-- url     : https://prove2.me/theorems/93da94da-b193-49d8-985c-6e252b5d6226
-- title:
--   Normalized bounded variation $NBV[a,b]$ (Luenberger's convention)
-- statement:
--   The normalized space $NBV[a,b]$ as Luenberger defines it in *Optimization by Vector Space Methods*, §5.5: a function $v$ of bounded variation on $[a,b]$ with $v(a)=0$ that is continuous from the right at every point of the **open** interval $(a,b)$.
--
--   This differs from `VectorSpaceOpt_is_nbv` only in the domain of the right-continuity requirement, which the latter takes to be $[a,b)$ — the left endpoint included. That single point matters. If $v(a)=0$ and $v$ is right-continuous at $a$, then $v(t)\to 0$ as $t\downarrow a$, so the first cell of any tagged partition contributes $x(\xi_0)\,(v(t_1)-v(a))\to x(a)\cdot 0 = 0$: a normalized $v$ can carry no atom at the left endpoint. Consequently the evaluation functional $x\mapsto x(a)$, which is a bounded linear functional on $C[a,b]$ of norm $1$, has no representative in that space, and the Riesz representation theorem fails. With the open-interval convention it is represented by $v=\chi_{(a,b]}$, whose total variation is $1$.
--
--   The norm on $NBV[a,b]$ is `VectorSpaceOpt_total_variation`, and the pairing with $C[a,b]$ is the Riemann–Stieltjes integral `VectorSpaceOpt_is_rs_integral`.
-- source:
--   D. G. Luenberger, Optimization by Vector Space Methods, Wiley 1969, §5.5, p. 113 (definition of NBV[a,b]) and Theorem 1 (Riesz representation for C[a,b]).

import Mathlib
import Definitions.Def_VectorSpaceOpt_bv_stieltjes

/-!
# The normalized space `NBV[a,b]`, with Luenberger's normalization

`VectorSpaceOpt_is_nbv` (in `Def_VectorSpaceOpt_bv_stieltjes`) asks for right
continuity on `Set.Ico a b`, i.e. on `[a, b)`, endpoint included.  Luenberger's
`NBV[a, b]` (Optimization by Vector Space Methods, §5.5) asks for it on the
**open** interval `(a, b)` only.

The difference is not cosmetic: with right continuity imposed at `a` as well,
`v a = 0` forces `v(a⁺) = 0`, so the first cell of any tagged partition
contributes `x(ξ₀)·(v t₁ - v a) → 0`.  A normalized `v` can then carry no atom
at the left endpoint, and the evaluation functional `x ↦ x a` — a perfectly good
element of `C[a,b]*` of norm `1` — has no representative.  With the open-interval
convention it does: `v = χ_(a,b]`.
-/

/-- `v` lies in the normalized space of functions of bounded variation
`NBV[a, b]`: of bounded variation on `[a, b]`, vanishing at `a`, and continuous
from the right at every **interior** point of `[a, b]`.  This is Luenberger's
normalization (§5.5); it is what makes the representation of a functional on
`C[a, b]` unique, and the norm on this space is `VectorSpaceOpt_total_variation`. -/
structure VectorSpaceOpt_is_nbv_open (a b : ℝ) (v : ℝ → ℝ) : Prop where
  boundedVariation : BoundedVariationOn v (Set.Icc a b)
  vanishes_at_left : v a = 0
  right_continuous : ∀ t ∈ Set.Ioo a b, ContinuousWithinAt v (Set.Ici t) t


