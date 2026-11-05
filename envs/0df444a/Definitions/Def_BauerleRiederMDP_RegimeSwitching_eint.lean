-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
-- name    : BauerleRiederMDP_RegimeSwitching_eint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:53.57116+00:00
-- url     : https://prove2.me/theorems/b32a3a15-262e-4576-ac38-64a8246d10d7
-- title:
--   Extended-real expectation $\int v\,d\mu = \int v^+ d\mu - \int v^- d\mu$
-- statement:
--   For a measure $\mu$ on a measurable space $\Omega$ and a function $v:\Omega\to[-\infty,\infty]$, the **expectation** of $v$ is
--
--   $$
--   \int v\,d\mu \;=\; \int v^+\,d\mu \;-\; \int v^-\,d\mu \;\in[-\infty,\infty],
--   $$
--
--   where $v^+=\max(v,0)$ and $v^-=\max(-v,0)$ are integrated as $[0,\infty]$-valued functions. This is the expectation used throughout the book's models: $\mathbb E^\pi_x$ and $\mathbb E^\pi_{nx}$ of §2.1 (p.17), and $\mathbb E^\pi_{xj}$ of the regime-switching models of §4.4 (p.102).
--
--   The definition needs no integrability side condition: an expected utility equal to $+\infty$ or $-\infty$ is recorded as such instead of being replaced by a default value.
--
--   The book's Integrability Assumption $(A_N)$ (§2.2, p.17) requires the positive parts of the rewards to have finite expectation, so on the book's models $\int v^+\,d\mu<\infty$ and the value lies in $[-\infty,\infty)$, which is exactly the book's expectation.
--
--   **Formalization Note** If both parts are infinite, Lean's extended-real convention $\infty-\infty=-\infty$ applies; under $(A_N)$ this case does not occur. For a non-measurable $v$ the lower Lebesgue integrals are used; every statement that imports this definition integrates measurable functions.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.1–§2.2, pp.16–17 (PDF pp.31–32): the expectations $\mathbb E^\pi_x$, $\mathbb E^\pi_{nx}$ and Integrability Assumption $(A_N)$

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- The expectation `𝔼[v] = ∫ v dμ ∈ [-∞, ∞]` of an extended-real-valued function, defined as
`∫⁻ v⁺ dμ - ∫⁻ v⁻ dμ` with the positive and negative parts taken in `[0, ∞]`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), the expectations `𝔼`, `𝔼^π_{xj}` of §2.1–§2.2, pp.16–17, PDF pp.31–32, and of §4.3–§4.4,
pp.93–105, PDF pp.107–119).

**Formalization Note.** No integrability side condition is needed: an expected utility that is
`+∞` or `-∞` is recorded as such, never replaced by a default value `0` (as a Bochner integral
would). Only when both parts are infinite does the `EReal` convention `⊤ - ⊤ = ⊥` apply; the
book's models never produce that case (rewards are bounded above by an affine function of the
wealth, which has finite mean under Assumption (FM)). -/
noncomputable def eint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → EReal) : EReal :=
  ((∫⁻ ω, (v ω).toENNReal ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ ω, (-v ω).toENNReal ∂μ : ℝ≥0∞) : EReal)

end BauerleRiederMDP.RegimeSwitching


