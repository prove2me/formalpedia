-- Prove2me | Definitions.Def_BousquetElisseeff_KLReg_avgLoss
-- name    : BousquetElisseeff_KLReg_avgLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:42:49.343379+00:00
-- url     : https://prove2.me/theorems/e8151a37-d86c-4f9f-b039-4718094f1334
-- title:
--   Averaged loss $\ell(g, z) = \int_\Theta r(h_\theta, z)\, g(\theta)\, d\theta$
-- statement:
--   Let $r(\theta, z)$ be the loss of the base hypothesis $h_\theta$ on the example $z$. For a density $g$ on $\Theta$ the **averaged loss** of the mixture $g$ on $z$ is
--   $$\ell(g, z) = \int_\Theta r(\theta, z)\, g(\theta)\, d\mu(\theta). \qquad (28)$$
--   It is the expected loss of the randomized algorithm that samples $h_\theta$ from the posterior $g$, and it is linear in $g$.
--
--   **Formalization Note** The base hypotheses enter only through $\theta \mapsto r(h_\theta, z)$, so the loss is a function $r : \Theta \to Z \to \mathbb R$ on an arbitrary type of examples $Z$. The theorems of the mission assume $r$ measurable in $\theta$ and bounded, so the integral is always the genuine one.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, §5.2.3, eq. (28), p. 517

import Mathlib

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **The averaged loss ℓ(g, z) = ∫_Θ r(h_θ, z) g(θ) dθ** (eq. (28)).
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526, §5.2.3, eq. (28),
p. 517: "or we can average the loss over Θ, ℓ(g, z) = ∫_Θ r(h_θ, z) g(θ)dθ. (28)"

Here `r θ z` is the base loss `r(h_θ, z)` of the base hypothesis `h_θ` on the example `z`, and
`avgLoss μ r g z = ∫ r θ z · g θ dμ(θ)` is the loss of the mixture with density `g`.

**Formalization Note.** The base hypotheses enter only through `θ ↦ r(h_θ, z)`, so the loss is
taken as a function `r : Θ → Z → ℝ` on an arbitrary type `Z` of examples. Every theorem of the
mission assumes `θ ↦ r θ z` measurable (p. 501: "all functions are measurable") and bounded, and
`g` a density, so the integrand is integrable and the Bochner integral is the paper's integral,
never the junk value `0`. -/
noncomputable def avgLoss {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ)
    (g : Θ → ℝ) (z : Z) : ℝ :=
  ∫ θ, r θ z * g θ ∂μ

end BousquetElisseeff.KLReg


