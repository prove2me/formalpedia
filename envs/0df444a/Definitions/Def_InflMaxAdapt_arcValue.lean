-- Prove2me | Definitions.Def_InflMaxAdapt_arcValue
-- name    : InflMaxAdapt_arcValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:58.424206+00:00
-- url     : https://prove2.me/theorems/9833e881-f5bb-40c6-a49d-efb8876bf264
-- title:
--   Expected influence $\mathbb E[\sigma(\pi)]$ of a policy (arc model)
-- statement:
--   The **influence** of an adaptive policy $\pi$ is $\sigma(\pi) = |C(S(\pi))|$, and its expectation is
--   $$
--   \mathbb E[\sigma(\pi)] \;=\; \int_\Omega \sum_{A \subseteq V^2} \mathbb P(A)\, \big|C_A(S_A(\pi, \omega))\big| \, d\mu(\omega),
--   $$
--   where $\omega \sim \mu$ is the external randomness, drawn independently of the live arc set $A$, and the seeds $S_A(\pi,\omega)$ are chosen with the full cascades $C_A(v_j)$ of the same realization $A$ as feedback.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib
import Definitions.Def_InflMaxAdapt_arcWeight
import Definitions.Def_InflMaxAdapt_arcCascade
import Definitions.Def_InflMaxAdapt_Policy_seeds

open MeasureTheory

namespace InflMaxAdapt

/-- The expected influence `E[σ(π)] = E|C(S(π))|` of an adaptive policy in the arc model
(Section 1.1, printed p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)). The external randomness `ω ∼ μ` is independent of the
live arc set `A`; for each `A` the policy receives the full cascades `C(v) = arcCascade A {v}` of the
same realization.

**Formalization Note** The expectation over `A` is the finite weighted sum; the expectation over
`ω` is the Bochner integral (the theorems assume the decision rules measurable and `μ` a
probability measure, so the integrand is a bounded measurable function). -/
noncomputable def arcValue {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (p : V → V → ℝ) (μ : Measure Ω) (π : Policy V k Ω) : ℝ :=
  ∫ ω, ∑ A : Finset (V × V),
    arcWeight p A * ((arcCascade A (π.seeds ω (fun v => arcCascade A {v}))).card : ℝ) ∂μ

end InflMaxAdapt


