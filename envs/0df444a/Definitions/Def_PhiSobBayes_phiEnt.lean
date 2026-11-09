-- Prove2me | Definitions.Def_PhiSobBayes_phiEnt
-- name    : PhiSobBayes_phiEnt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:03.957064+00:00
-- url     : https://prove2.me/theorems/e833405d-74c5-4a26-ba36-cc99e5eac8c5
-- title:
--   $\Phi$-entropy $\mathrm{Ent}^\Phi_\mu(f)$
-- statement:
--   For a measure $\mu$, a function $\Phi:\mathbb R\to\mathbb R$ and a real function $f$, the **$\Phi$-entropy** of $f$ under $\mu$ is
--   $$\mathrm{Ent}^\Phi_\mu(f)=\mathbb E_\mu\Phi(f)-\Phi(\mathbb E_\mu f).$$
--
--   For $\Phi(z)=(z-1)^2$ it is the variance $\mathrm{Var}_\mu(f)$, and for $\Phi(z)=z\log z$ it is the entropy $\mathrm{Ent}_\mu(f)$. For convex $\Phi$ and a probability measure it is nonnegative by Jensen's inequality. In the mission it is applied to the prior, to posteriors and to observation laws.
--
--   **Formalization Note** Defined on any measurable space with Bochner integrals. For test functions every integrand is bounded and continuous; results applied to other functions state the integrability they need.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 1, p.3 (PDF 3)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- The **Φ-entropy** `Ent^Φ_μ(f) = 𝔼_μ Φ(f) − Φ(𝔼_μ f)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 1, p.3 (PDF 3): "Their so-called Φ-entropy functional is given by
EntΦ_𝜇(𝑓) = 𝔼𝜇Φ(𝑓) − Φ(𝔼𝜇𝑓)".

**Formalization Note** Bochner integrals on an arbitrary measurable space (the paper applies the
functional to the prior, to posteriors and to observation laws). For test functions every
integrand is bounded and continuous, so both integrals are honest; the milestones that use other
functions state the integrability they need. -/
noncomputable def phiEnt {α : Type*} [MeasurableSpace α] (μ : Measure α) (Φ : ℝ → ℝ)
    (f : α → ℝ) : ℝ :=
  ∫ x, Φ (f x) ∂μ - Φ (∫ x, f x ∂μ)

end PhiSobBayes


