-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_expectedGap
-- name    : FoundationsRL_E2DStructured_expectedGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:50.512326+00:00
-- url     : https://prove2.me/theorems/595b115d-c17d-4136-a2ff-d88fd70ee235
-- title:
--   The expected regret $\mathbb E_{\pi\sim p}[f(\pi_f)-f(\pi)]$
-- statement:
--   For a reward function $f$ and a distribution $p\in\Delta(\Pi)$, the expected regret of $p$ under $f$ is
--   $$\mathbb E_{\pi\sim p}\big[f(\pi_f)-f(\pi)\big]\in[0,\infty].$$
--   It is the first term of the objective in the Decision-Estimation Coefficient, and the per-round summand of the regret.
--
--   **Formalization Note** The expectation is a Lebesgue integral of a nonnegative function with values in $[0,\infty]$; it is $+\infty$ when $f$ is not integrable under $p$. Lean's Bochner integral would return $0$ in that case.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_maxValue

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The expected regret of a decision distribution, `E_{π∼p}[f(π_f) − f(π)]`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65, (4.15), first term).

**Formalization Note.** Written as a `lintegral`: for `f` with a maximizer the integrand is
nonnegative, so the expectation is a well-defined element of `[0, ∞]`, including when `f` is
unbounded below and `E_{π∼p}[f]` is `−∞` (a Bochner integral would return the junk value `0`). -/
noncomputable def expectedGap {D : Type*} [MeasurableSpace D] (f : D → ℝ)
    (p : ProbabilityMeasure D) : ℝ≥0∞ :=
  ∫⁻ π, ENNReal.ofReal (maxValue f - f π) ∂(p : Measure D)

end FoundationsRL.E2DStructured


