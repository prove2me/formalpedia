-- Prove2me | Definitions.Def_SDEConvexOpt_InS
-- name    : SDEConvexOpt_InS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:31.39943+00:00
-- url     : https://prove2.me/theorems/6d46c779-a496-4ff3-ba51-94623e03d095
-- title:
--   The moment condition of $S^\nu_d$: $\mathbb E\sup_{t\le T}\|X(t)\|^\nu<\infty$ for all $T$
-- statement:
--   For $\nu>0$, a process $X$ satisfies the moment condition of the class $S^\nu_d=\bigcap_{T\ge0}S^\nu_d[0,T]$ when
--   $$
--   \mathbb E\Big(\sup_{t\in[0,T]}\|X(t)\|^\nu\Big)<+\infty\qquad\text{for every } T\ge0 .
--   $$
--
--   **Formalization Note** The expectation is a lower Lebesgue integral in $[0,\infty]$ and $\nu$ is a real exponent. The rest of the definition of $S^\nu_d$ (continuity, progressive measurability) comes from `SolvesSDE`, with which the predicate is always used.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, §2.2, p.7

import Definitions.Def_EthierKurtz_SDEState

open MeasureTheory
open scoped NNReal ENNReal

namespace SDEConvexOpt

open EthierKurtz

/-- The moment condition of the class `S^ν_d = ⋂_{T ≥ 0} S^ν_d[0, T]`
(Maulen S., Fadili, Attouch, arXiv:2207.02750v1, §2.2, p.7):
`𝔼(sup_{t ∈ [0, T]} ‖X(t)‖^ν) < +∞` for every `T ≥ 0`.

**Formalization Note** The expectation of the nonnegative quantity is a lower Lebesgue integral
in `ℝ≥0∞`, and `ν` is a real exponent (`rpow`). Continuity and progressive measurability, the rest
of the definition of `S^ν_d`, come with `SolvesSDE`, with which this predicate is always used. -/
def InS {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (ν : ℝ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  ∀ T : ℝ≥0, ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : t ≤ T), ‖X t ω‖ₑ ^ ν) ∂P < ∞

end SDEConvexOpt


