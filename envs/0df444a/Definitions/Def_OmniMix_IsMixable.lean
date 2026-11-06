-- Prove2me | Definitions.Def_OmniMix_IsMixable
-- name    : OmniMix_IsMixable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:52.126287+00:00
-- url     : https://prove2.me/theorems/9087a624-b07e-42a5-b73f-358170d3a314
-- title:
--   $\beta$-mixable loss
-- statement:
--   Let $\beta\in\mathbb R$. A loss $\ell$ is **$\beta$-mixable** if for every probability distribution $D$ over $[0,1]$ there is a prediction $p\in[0,1]$ such that
--   $$
--   e^{-\beta\ell(p,y)}\ \ge\ \mathbb E_{P\sim D}\,e^{-\beta\ell(P,y)}\qquad\text{for both }y\in\{0,1\},
--   $$
--   with the convention $e^{-\infty}=0$.
--
--   Squared loss is $2$-mixable and log loss is $1$-mixable. The paper's $\beta^\star_\ell$ is the largest such $\beta$; the formalization does not define it and quantifies over every $\beta>0$ at which $\ell$ is mixable instead.
--
--   **Formalization Note** Distributions are Borel probability measures on $[0,1]$. The exponential is the extended exponential $\mathrm{EReal}\to[0,\infty]$, and the expectation is the Lebesgue integral of a $[0,\infty]$-valued function (`lintegral`), so no integrability side condition can make it vanish.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1 and §2, p.9

import Mathlib
import Definitions.Def_OmniMix_Loss

namespace OmniMix

/-- **β-mixable loss.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1 and §2, p.9: "a loss `ℓ` is β-mixable if, for
every distribution `D` over `[0, 1]`, there exists `p ∈ [0, 1]` such that
`exp(−βℓ(p, y)) ≥ E_{P∼D} exp(−βℓ(P, y)), ∀y ∈ {0, 1}`".

**Formalization Note.** A distribution over `[0,1]` is a Borel probability measure `μ` on
`unitInterval`. The exponential is `EReal.exp : EReal → ℝ≥0∞` applied to `−(β·ℓ)`, so
`exp(−β·(+∞)) = 0` for `β > 0`; the expectation is the lower Lebesgue integral `∫⁻`, never a Bochner
integral (which would be `0` for a non-integrable integrand). The largest such `β`, the paper's
`β⋆_ℓ`, is not defined: theorems quantify over every `β > 0` at which `ℓ` is β-mixable. -/
def IsMixable (β : ℝ) (ℓ : Loss) : Prop :=
  ∀ μ : MeasureTheory.Measure unitInterval, MeasureTheory.IsProbabilityMeasure μ →
    ∃ p : unitInterval, ∀ y : Bool,
      ∫⁻ q, EReal.exp (-((β : EReal) * ℓ q y)) ∂μ ≤ EReal.exp (-((β : EReal) * ℓ p y))

end OmniMix


