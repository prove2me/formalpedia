-- Prove2me | Definitions.Def_BewleyGE_WeakConv
-- name    : BewleyGE_WeakConv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:34.258604+00:00
-- url     : https://prove2.me/theorems/d9486e95-f0a1-4ad9-86c8-528c4238558d
-- title:
--   Weak convergence of measures on $\mathbb R$
-- statement:
--   A sequence of measures $\nu_k$ on $\mathbb R$ **converges weakly** to $\nu_0$ if
--   $$
--   \int f\,d\nu_k\to\int f\,d\nu_0\qquad\text{for every bounded continuous }f:\mathbb R\to\mathbb R .
--   $$
--   For probability measures this is the usual weak convergence.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Lemmas 2–4, pp.21–24

import Mathlib

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace BewleyGE

/-- **Weak convergence of measures on `ℝ`**: `∫ f dνₖ → ∫ f dν₀` for every bounded continuous
`f : ℝ → ℝ`. Light, arXiv:1906.06810v2, Lemmas 2–4, pp.21–24 ("converges weakly").

**Formalization Note.** For probability measures this is the usual weak convergence (the topology
of `MeasureTheory.ProbabilityMeasure ℝ`); it is stated on `Measure ℝ` so that the wealth operator
can be iterated without coercions. -/
def WeakConv (ν : ℕ → Measure ℝ) (ν₀ : Measure ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, Tendsto (fun k => ∫ a, f a ∂(ν k)) atTop (𝓝 (∫ a, f a ∂ν₀))

end BewleyGE


