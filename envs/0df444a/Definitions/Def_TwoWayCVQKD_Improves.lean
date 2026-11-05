-- Prove2me | Definitions.Def_TwoWayCVQKD_Improves
-- name    : TwoWayCVQKD_Improves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:46.532078+00:00
-- url     : https://prove2.me/theorems/b9bdac97-11a8-4db6-ab75-8e900946ecfe
-- title:
--   Comparison of security thresholds of two rate functions
-- statement:
--   Security thresholds are the boundary conditions $R=0$ of a rate. For two rate functions $r_1,r_2$ of the EPR variance $W\ge1$ at a fixed transmission, the statement "$r_2$ improves on $r_1$" has two clauses:
--
--   1. $r_2(W)>0$ at every $W\ge1$ with $r_1(W)\ge0$: the second scheme is strictly secure wherever the first is secure, including at the first scheme's threshold;
--   2. if $r_2(W)>0$ for some $W\ge1$, then there is a $W\ge1$ with $r_1(W)<0<r_2(W)$: the second scheme's secure region extends beyond the first's.
--
--   **Formalization Note** At fixed $T\in(0,1)$ the excess noise $N=(W-1)(1-T)/T$ is an increasing bijection of $[1,\infty)$ onto $[0,\infty)$, so the same comparison holds on the $N$ axis of Figs. 2 and 3. The strict inequality in clause 1 rules out equal thresholds.
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, p.2 (thresholds, excess noise) and p.4 (comparison of thresholds)

import Mathlib

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, p.2 and p.4: `r₂` has a better
security threshold than `r₁` at a fixed transmission, where a threshold is the boundary `R = 0`
(p.2) and the noise axis is `W ≥ 1`.

**Formalization Note** The first clause says `r₂` is strictly secure wherever `r₁` is secure,
including at the threshold of `r₁`. The second says that if `r₂` is ever secure, then it is secure
at some `W` where `r₁` is not. When `r₂` is never secure both thresholds vanish and the comparison
holds by the first clause only if `r₁` is never secure either. At fixed `T ∈ (0, 1)` the excess noise
`N = (W - 1)(1 - T)/T` is an increasing bijection of `W ∈ [1, ∞)` onto `[0, ∞)`, so the comparison
is the same in `N`. -/
def Improves (r₁ r₂ : ℝ → ℝ) : Prop :=
  (∀ W, 1 ≤ W → 0 ≤ r₁ W → 0 < r₂ W) ∧
    ((∃ W, 1 ≤ W ∧ 0 < r₂ W) → ∃ W, 1 ≤ W ∧ r₁ W < 0 ∧ 0 < r₂ W)

end TwoWayCVQKD


