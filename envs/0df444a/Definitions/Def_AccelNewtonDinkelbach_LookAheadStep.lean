-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_LookAheadStep
-- name    : AccelNewtonDinkelbach_LookAheadStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:46.277078+00:00
-- url     : https://prove2.me/theorems/ea8fcfe9-ae92-408b-be47-6315ffb80b8e
-- title:
--   One iteration of Algorithm 1 (Look-aheadNewton)
-- statement:
--   Let $f$ be a proper concave function, accessed through a value oracle and a supergradient oracle. One iteration of **Algorithm 1 (Look-aheadNewton)** starts from the current point $\delta^{(i)}$ and supergradient $g^{(i)}$ and runs:
--
--   1. continue only if $f(\delta^{(i)})<0$ (line 2);
--   2. $\delta\leftarrow\delta^{(i)}-f(\delta^{(i)})/g^{(i)}$ and query $g\in\partial f(\delta)$ (lines 3–4);
--   3. if $f(\delta)=-\infty$, or $f(\delta)<0$ and $g\ge 0$, return NO ROOT (lines 5–6);
--   4. form the look-ahead guess $\delta'=2\delta-\delta^{(i)}$ and query $g'\in\partial f(\delta')$ (lines 7–8);
--   5. if $-\infty<f(\delta')<0$ and $g'<0$ (the look-ahead is **successful**), replace $(\delta,g)$ by $(\delta',g')$ (lines 9–10);
--   6. set $\delta^{(i+1)}\leftarrow\delta$, $g^{(i+1)}\leftarrow g$ (line 11).
--
--   The predicate says that $(\delta^{(i+1)},g^{(i+1)})$ can be the outcome of such an iteration from $(\delta^{(i)},g^{(i)})$ for some answers of the supergradient oracle. Either the look-ahead succeeds and the next pair is $(\delta',g')$ with $\delta'\in\operatorname{dom}(f)$, $f(\delta')<0$, $g'\in\partial f(\delta')$, $g'<0$; or the oracle's answer at $\delta'$ fails the test of line 9 ($f(\delta')=-\infty$, no supergradient exists, or the returned $g'$ violates $f(\delta')<0$ and $g'<0$) and the next pair is the plain Newton–Dinkelbach pair $(\delta,g)$.
--
--   **Formalization Note** "$f(x)=-\infty$" is $x\notin$ `dom`. The oracle answers are arbitrary at every call (existentially chosen). If the Newton point lies in `dom` but has no supergradient, line 4 cannot be executed and no next iterate exists; if the look-ahead guess lies in `dom` but has no supergradient, the look-ahead fails.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Algorithm 1 and the paragraph above it, p.7

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_superdiff
import Definitions.Def_AccelNewtonDinkelbach_newtonPoint

namespace AccelNewtonDinkelbach

/-- **One iteration of Algorithm 1 (Look-aheadNewton), with arbitrary oracle answers.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Algorithm 1, lines 2–11, p.7, and the paragraph
above it ("If −∞ < f(δ′) < 0 and g′ < 0, then the next point and supergradient are set to
δ(i+1) := δ′ and g(i+1) := g′ … Otherwise, we proceed as usual by taking δ(i+1) := δ and
g(i+1) := g").

`LookAheadStep dom f δ g δ' g'` says that an iteration of Algorithm 1 started at the current point
`δ` with current supergradient `g` can end with next point `δ'` and next supergradient `g'`, for
some answers of the supergradient oracle. With `d = δ − f δ / g` (line 3) and look-ahead guess
`ℓ = 2d − δ` (line 7), this holds iff

1. `δ ∈ dom` and `f δ < 0` (the loop test of line 2);
2. `d ∈ dom` (so `f(d) ≠ −∞`, first test of line 5);
3. the oracle returns some `gd ∈ ∂f(d)` (line 4) with not (`f d < 0` and `gd ≥ 0`) (second test of
   line 5), so the algorithm does not return NO ROOT; and
4. either the look-ahead is **successful**: `ℓ ∈ dom`, `f ℓ < 0`, the oracle returns `g' ∈ ∂f(ℓ)`
   with `g' < 0`, and `δ' = ℓ` (lines 8–11); or it **fails**: `δ' = d`, `g' = gd`, and the oracle's
   answer at `ℓ` does not pass line 9's test, i.e. `ℓ ∉ dom` (`f(ℓ) = −∞`), or `∂f(ℓ) = ∅` (no
   answer), or some `h ∈ ∂f(ℓ)` with not (`f ℓ < 0` and `h < 0`) is returned.

**Formalization Note** `(dom, f)` encodes a proper concave `f : ℝ → ℝ̄` (see `superdiff`), so
"`f(x) = −∞`" is `x ∉ dom`. The oracle is arbitrary at every call: the answers `gd` and `g'`/`h`
are existentially chosen. If `∂f(d) = ∅` while `d ∈ dom`, line 4 cannot be executed and no next
iterate exists; if `∂f(ℓ) = ∅` while `ℓ ∈ dom`, the look-ahead counts as failed. -/
def LookAheadStep (dom : Set ℝ) (f : ℝ → ℝ) (δ g δ' g' : ℝ) : Prop :=
  let d := newtonPoint f δ g
  let ℓ := 2 * d - δ
  δ ∈ dom ∧ f δ < 0 ∧ d ∈ dom ∧
    ∃ gd ∈ superdiff dom f d, ¬ (f d < 0 ∧ 0 ≤ gd) ∧
      ((ℓ ∈ dom ∧ f ℓ < 0 ∧ g' ∈ superdiff dom f ℓ ∧ g' < 0 ∧ δ' = ℓ) ∨
        (δ' = d ∧ g' = gd ∧
          (ℓ ∉ dom ∨ superdiff dom f ℓ = ∅ ∨
            ∃ h ∈ superdiff dom f ℓ, ¬ (f ℓ < 0 ∧ h < 0))))

end AccelNewtonDinkelbach


