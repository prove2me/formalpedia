-- Prove2me | Definitions.Def_RedundancyHT_ConvergesInLaw
-- name    : RedundancyHT_ConvergesInLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:43.438964+00:00
-- url     : https://prove2.me/theorems/86baf392-a796-4fdd-b137-5192ae55a7c7
-- title:
--   Convergence in distribution along a filter
-- statement:
--   Measures $\mu_a$ on $\mathbb R^n$ converge in distribution to $\nu$ along a filter $l$ if
--   $$\int f\,d\mu_a\longrightarrow\int f\,d\nu$$
--   along $l$ for every bounded continuous $f:\mathbb R^n\to\mathbb R$. For probability measures this is the usual meaning of $\xrightarrow{d}$.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, Theorem 2, p.12

import Mathlib

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **Convergence in distribution** of measures on `ℝⁿ` along a filter
(arXiv:2005.14566v5, Theorem 2, p.12): integrals of bounded continuous functions converge.

**Formalization Note.** The filter is arbitrary, so `λ ↑ λ*` is `𝓝[<] λ*`. The statements using
this have probability measures on both sides, at least eventually along the filter, so the integrals
are genuine: a bounded measurable function is integrable against a finite measure. -/
def ConvergesInLaw {ι : Type} {n : ℕ} (μ : ι → Measure (Fin n → ℝ)) (l : Filter ι)
    (ν : Measure (Fin n → ℝ)) : Prop :=
  ∀ f : (Fin n → ℝ) →ᵇ ℝ, Tendsto (fun a => ∫ x, f x ∂(μ a)) l (𝓝 (∫ x, f x ∂ν))

end RedundancyHT


