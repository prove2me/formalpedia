-- Prove2me | Definitions.Def_MemQueryFeas_HasCondLaw
-- name    : MemQueryFeas_HasCondLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:39.049009+00:00
-- url     : https://prove2.me/theorems/caad7433-3240-4291-8c26-2cf8813f1d42
-- title:
--   Prescribed conditional law
-- statement:
--   A random variable $X$ has **conditional law $\kappa(H)$ given $H$** if for all measurable sets $A$ and $B$
--   $$
--   \Pr(X\in A,\ H\in B)=\mathbb E\big[\kappa(H)(A)\,\mathbf 1\{H\in B\}\big].
--   $$
--   This is how the sampling steps "sample $X\sim\kappa(H)$" of the construction are expressed.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 1, p.8 (PDF p.9)

import Mathlib

open MeasureTheory

namespace MemQueryFeas

/-- **Conditional law given a random variable.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 1, p.8 (PDF p.9): steps of the form
"Sample `F^(i) ∼ Unif(B(F^(i+1), δ^(i)))`", i.e. statements that a random variable has a prescribed
conditional law given the variables sampled before it.

`HasCondLaw μ X H κ`: the conditional law of `X` given `H` is `κ(H)`, in the disintegration form
`μ(X ∈ A, H ∈ B) = ∫_{H ∈ B} κ(H(ω))(A) dμ(ω)` for all measurable `A`, `B`.

**Formalization Note.** Stated without Markov kernels, so the measurability of `κ` is not part of the
definition; in every use `κ` is a measurable family and `X`, `H` are measurable. -/
def HasCondLaw {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure Ω) (X : Ω → γ) (H : Ω → β) (κ : β → Measure γ) : Prop :=
  ∀ A : Set γ, MeasurableSet A → ∀ B : Set β, MeasurableSet B →
    μ (X ⁻¹' A ∩ H ⁻¹' B) = ∫⁻ ω in H ⁻¹' B, κ (H ω) A ∂μ

end MemQueryFeas


