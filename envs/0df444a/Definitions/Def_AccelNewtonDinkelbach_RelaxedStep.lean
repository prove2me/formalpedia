-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_RelaxedStep
-- name    : AccelNewtonDinkelbach_RelaxedStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:53.082216+00:00
-- url     : https://prove2.me/theorems/8bb5619a-26dc-4d16-ae81-0ba5d5d6e235
-- title:
--   One Newton–Dinkelbach iteration, with or without look-ahead
-- statement:
--   A **relaxed step** from $(\delta^{(i)},g^{(i)})$ to $(\delta^{(i+1)},g^{(i+1)})$ is an iteration in which, as in Algorithm 1, $f(\delta^{(i)})<0$, the Newton–Dinkelbach point $\delta=\delta^{(i)}-f(\delta^{(i)})/g^{(i)}$ lies in $\operatorname{dom}(f)$, and some oracle answer $g\in\partial f(\delta)$ does not trigger NO ROOT (not both $f(\delta)<0$ and $g\ge0$); and then the next pair is either
--
--   1. a successful look-ahead $(\delta',g')$ with $\delta'=2\delta-\delta^{(i)}\in\operatorname{dom}(f)$, $f(\delta')<0$, $g'\in\partial f(\delta')$, $g'<0$, or
--   2. the standard update $(\delta,g)$,
--
--   with the choice left free. Runs of relaxed steps contain the runs of the classical Newton–Dinkelbach method (always option 2), for which Lemmas 3.1 and 3.3 of the paper are proved, and the runs of Algorithm 1, for which the paper states that these lemmas also hold.
--
--   **Formalization Note** Same encoding of $f$ and of the oracle as for Algorithm 1's step. Unlike Algorithm 1, the standard update is allowed even when the look-ahead would have succeeded.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6 (the standard method) and p.7 ("Lemmas 3.1 and 3.3 also hold for Algorithm 1")

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_superdiff
import Definitions.Def_AccelNewtonDinkelbach_newtonPoint

namespace AccelNewtonDinkelbach

/-- **One iteration of the Newton–Dinkelbach method, with or without look-ahead.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, §3, p.6 (the standard method: "a new point
δ := δ(i) − f(δ(i))/g(i) is generated … If both scenarios do not apply, the next point and
supergradient is set to δ(i+1) := δ and g(i+1) := g") and p.7 ("It is easy to verify that Lemmas
3.1 and 3.3 also hold for Algorithm 1").

`RelaxedStep dom f δ g δ' g'` holds iff, with `d = δ − f δ / g` and `ℓ = 2d − δ`,

1. `δ ∈ dom` and `f δ < 0`;
2. `d ∈ dom`;
3. some oracle answer `gd ∈ ∂f(d)` has not (`f d < 0` and `gd ≥ 0`) (the method does not report
   NO ROOT); and
4. either `ℓ ∈ dom`, `f ℓ < 0`, `g' ∈ ∂f(ℓ)`, `g' < 0` and `δ' = ℓ` (a successful look-ahead), or
   `δ' = d` and `g' = gd` (a standard Newton–Dinkelbach update).

Unlike `LookAheadStep`, the standard update is allowed even when a look-ahead would have succeeded.
So a run of relaxed steps covers both the standard method of p.6, for which Lemmas 3.1 and 3.3 are
proved, and Algorithm 1, for which p.7 says they also hold.

**Formalization Note** `(dom, f)` encodes a proper concave `f : ℝ → ℝ̄` (see `superdiff`); the
oracle answers are existentially chosen; if `∂f(d) = ∅` while `d ∈ dom`, no next iterate exists. -/
def RelaxedStep (dom : Set ℝ) (f : ℝ → ℝ) (δ g δ' g' : ℝ) : Prop :=
  let d := newtonPoint f δ g
  let ℓ := 2 * d - δ
  δ ∈ dom ∧ f δ < 0 ∧ d ∈ dom ∧
    ∃ gd ∈ superdiff dom f d, ¬ (f d < 0 ∧ 0 ≤ gd) ∧
      ((ℓ ∈ dom ∧ f ℓ < 0 ∧ g' ∈ superdiff dom f ℓ ∧ g' < 0 ∧ δ' = ℓ) ∨
        (δ' = d ∧ g' = gd))

end AccelNewtonDinkelbach


