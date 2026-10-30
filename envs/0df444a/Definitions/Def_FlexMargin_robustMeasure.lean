-- Prove2me | Definitions.Def_FlexMargin_robustMeasure
-- name    : FlexMargin_robustMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:34:11.93499+00:00
-- url     : https://prove2.me/theorems/93bb7d0a-f6b2-448c-80bf-8c5961f53115
-- title:
--   Robust (worst-case) measure $R^f(\mathcal A, U)$
-- statement:
--   For a deterministic measure $f$, which assigns a real number $f(\mathcal A,d)$ to a design and a demand vector, and an uncertainty set $U$ of demand vectors, the **robust measure** is the worst case
--
--   $$
--   R^f(\mathcal A,U)=\inf_{d\in U} f(\mathcal A,d).
--   $$
--
--   The paper writes a minimum and assumes $f$ continuous in $d$ so that it is attained.
--
--   **Formalization Note** The infimum is taken in the extended reals; it equals the paper's minimum whenever that exists, is $+\infty$ for $U=\emptyset$, and no continuity is assumed.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §2.2, p. 13

import Mathlib

namespace FlexMargin

/-- **Robust (worst-case) measure `R^f(𝒜, U)`.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §2.2, p. 13: "Given a deterministic measure function f, we denote Rf(·) as the robust
measure of f, which is defined as the worst-case performance among all possible demand instances
in a given uncertainty set U: Rf(A,U) := min_{d∈U} f(d,A)."

For a deterministic measure `f` (a real number for each design and demand vector), a design `A`
and an uncertainty set `U` of demand vectors, `robustMeasure f A U` is the infimum of `f A d` over
`d ∈ U`, computed in the extended reals.

**Formalization Note.** The paper assumes `f` continuous in `d` "which ensures that its robust
counterpart Rf(·) is always well defined", i.e. that the minimum exists. The infimum in `EReal`
equals that minimum whenever it exists and is defined for every `U` (it is `⊤` for `U = ∅` and may
be `⊥` for unbounded `f`); no continuity is assumed. -/
noncomputable def robustMeasure {m n : ℕ} (f : Finset (Fin m × Fin n) → (Fin n → ℝ) → ℝ)
    (A : Finset (Fin m × Fin n)) (U : Set (Fin n → ℝ)) : EReal :=
  ⨅ d ∈ U, ((f A d : ℝ) : EReal)

end FlexMargin


