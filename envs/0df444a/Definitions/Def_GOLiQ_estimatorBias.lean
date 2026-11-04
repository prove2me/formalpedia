-- Prove2me | Definitions.Def_GOLiQ_estimatorBias
-- name    : GOLiQ_estimatorBias
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:34.83422+00:00
-- url     : https://prove2.me/theorems/636da2ef-dd74-4324-8bfd-afbe45174588
-- title:
--   Bias $B_k=\mathbb E[\|\mathbb E[H_k-\nabla f(x_k)\mid\mathcal F_k]\|^2]^{1/2}$ of a gradient estimator
-- statement:
--   For gradient estimators $H_k$ at iterates $x_k$, a gradient field $g=\nabla f$ and σ-algebras $\mathcal F_k$, the **bias** of iteration $k$ is
--   $$B_k=\mathbb E\big[\|\mathbb E[H_k-\nabla f(x_k)\mid\mathcal F_k]\|^2\big]^{1/2}.\tag{4}$$
--
--   It measures the systematic error of the estimator given the past.
--
--   **Formalization Note** The outer expectation is a lower Lebesgue integral in $[0,\infty]$; the inner one is a conditional expectation.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, (4), p.13

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives

open MeasureTheory

namespace GOLiQ

/-- **The bias `Bₖ` of a gradient estimator** (Chen, Liu, Hong, arXiv:2009.02911v3, (4), p.13):

`Bₖ = E[‖E[Hₖ − ∇f(xₖ) | 𝓕ₖ]‖²]^{1/2}`,

for estimators `Hₖ`, iterates `xₖ`, gradient field `g = ∇f` and σ-algebras `𝓕ₖ`.

**Formalization Note.** The outer expectation is a lower Lebesgue integral in `[0, ∞]`; the
conditional expectation is Mathlib's `condExp`. -/
noncomputable def estimatorBias {Ω : Type*} [MeasurableSpace Ω] (Pr : Primitives Ω)
    (F : ℕ → MeasurableSpace Ω) (g : Point → Point) (x H : ℕ → Ω → Point) (k : ℕ) : ENNReal :=
  (∫⁻ ω, ‖(Pr.P[fun ω' => H k ω' - g (x k ω') | F k]) ω‖ₑ ^ 2 ∂Pr.P) ^ (1 / 2 : ℝ)

end GOLiQ


