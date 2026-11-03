-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_condExp
-- name    : EnvelopeMSLP_MSLP_condExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:32.485327+00:00
-- url     : https://prove2.me/theorems/3aa3c2fe-41c7-49b6-b098-1d8d5943acbd
-- title:
--   Conditional expectation given the history
-- statement:
--   For an extended-real function $f$ on scenarios,
--   $$\mathbb E[f\mid\xi^i](\omega)=\sum_{\omega'\sim\omega}\frac{p(\omega')}{\mathbb P(\text{class of }\omega)}f(\omega'),$$
--   over the scenarios with the history of $\omega$.
--
--   **Formalization Note** The sum is in `EReal` with positive real weights. Since $\bot+\top=\bot$, the result is $-\infty$ as soon as one scenario of the class has value $-\infty$: an infeasible child makes a decision infeasible even if another child is unbounded.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (8), p.12

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_SameHistory

namespace EnvelopeMSLP

/-- **Conditional expectation of an extended-real function given the history** `ξ^i` of `ω`:
`E[f | ξ^i](ω) = Σ_{ω' ~ ω} (p(ω') / P(class of ω)) f(ω')`. Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (8), p.12.

**Formalization Note.** The sum is in `EReal`, and every weight is a positive real. Since `⊥ + ⊤ = ⊥`,
the result is `⊥` as soon as one scenario of the class has value `⊥`, which is the right convention:
an infeasible child makes the decision infeasible, even if another child is unbounded. -/
noncomputable def MSLP.condExp {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (i : Fin (T + 1)) (f : Ω → EReal) (ω : Ω) : EReal :=
  open Classical in
  ∑ ω' ∈ Finset.univ.filter (P.SameHistory i ω),
    ((P.p ω' / ∑ ω'' ∈ Finset.univ.filter (P.SameHistory i ω), P.p ω'' : ℝ) : EReal) * f ω'

end EnvelopeMSLP


