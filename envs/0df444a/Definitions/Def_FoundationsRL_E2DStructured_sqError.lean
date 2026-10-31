-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_sqError
-- name    : FoundationsRL_E2DStructured_sqError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:49.827174+00:00
-- url     : https://prove2.me/theorems/70191820-223c-48f2-a84e-ab683d90946c
-- title:
--   The squared distance $\mathbb E_{\pi\sim p}[(g(\pi)-h(\pi))^2]$
-- statement:
--   For two functions $g,h:\Pi\to\mathbb R$ and a distribution $p\in\Delta(\Pi)$, the squared distance under $p$ is
--   $$\mathbb E_{\pi\sim p}\big[(g(\pi)-h(\pi))^2\big]\in[0,\infty].$$
--   It is the information term of the Decision-Estimation Coefficient and the per-round summand of the estimation error of Definition 7.
--
--   **Formalization Note** The expectation is a Lebesgue integral with values in $[0,\infty]$, so a function that is not square-integrable under $p$ has squared distance $+\infty$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65; Definition 7, p. 64

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The squared distance `E_{π∼p}[(g(π) − h(π))²]` between two reward functions under a decision
distribution (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65, (4.15), and Definition 7, p. 64).

**Formalization Note.** A `lintegral` of a nonnegative integrand, with values in `[0, ∞]`: a reference
model that is not square-integrable under `p` has infinite squared error, not the Bochner junk value
`0`. -/
noncomputable def sqError {D : Type*} [MeasurableSpace D] (p : ProbabilityMeasure D)
    (g h : D → ℝ) : ℝ≥0∞ :=
  ∫⁻ π, ENNReal.ofReal ((g π - h π) ^ 2) ∂(p : Measure D)

end FoundationsRL.E2DStructured


