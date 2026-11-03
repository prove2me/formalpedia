-- Prove2me | Definitions.Def_DRAllocCV_markovSet
-- name    : DRAllocCV_markovSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:50.259085+00:00
-- url     : https://prove2.me/theorems/689d540e-7bad-421d-b0b2-c42cfa2d73bd
-- title:
--   Markov ambiguity set (5): means in $[\underline\mu_i,\overline\mu_i]$
-- statement:
--   The **Markov ambiguity set** contains every probability distribution on the type space whose mean type of each agent lies in a prescribed interval:
--
--   $$
--   \mathcal P=\Bigl\{\mathbb P\in\mathcal P_0(\mathcal T):\ \mathbb E_{\mathbb P}[\tilde t_i]\in[\underline\mu_i,\overline\mu_i]\ \ \forall i\in\mathcal I\Bigr\},
--   $$
--
--   where $\underline\mu_i$ and $\overline\mu_i$ are lower and upper bounds on agent $i$'s expected type. The paper assumes $\underline t_i<\underline\mu_i<\overline\mu_i<\overline t_i$ for all $i$; types may be arbitrarily dependent under $\mathbb P$.
--
--   **Formalization Note** A distribution on $\mathcal T$ is a probability measure on $\mathbb R^I$ giving the complement of $\mathcal T$ measure zero. The standing assumption on the bounds is a hypothesis of each theorem, not part of the set.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §4, p.14, eq. (5)

import Mathlib
import Definitions.Def_DRAllocCV_typeSpace

open MeasureTheory

namespace DRAllocCV

/-- The **Markov ambiguity set** (5) (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §4, p.14):
`𝒫 = {ℙ ∈ 𝒫₀(𝒯) : 𝔼_ℙ[t̃ᵢ] ∈ [µ̲ᵢ, µ̄ᵢ] ∀ i ∈ ℐ}`, all probability distributions on the type
space whose mean type of each agent `i` lies between the lower bound `µ̲ᵢ = mlo i` and the upper
bound `µ̄ᵢ = mhi i`.

**Formalization Note.** A distribution on `𝒯` is a probability measure `ℙ` on `ι → ℝ` with
`ℙ(𝒯ᶜ) = 0` (equivalent, since `𝒯` is closed). The mean `𝔼_ℙ[t̃ᵢ]` is the Bochner integral of the
`i`-th coordinate, which is integrable because `ℙ` is concentrated on the bounded box `𝒯`. The
paper's standing assumption `t̲ᵢ < µ̲ᵢ < µ̄ᵢ < t̄ᵢ` (p.14) is a hypothesis of every theorem about
this set, not part of the definition. -/
def markovSet {ι : Type*} (tlo thi mlo mhi : ι → ℝ) : Set (Measure (ι → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (typeSpace tlo thi)ᶜ = 0 ∧
    ∀ i, ∫ t, t i ∂P ∈ Set.Icc (mlo i) (mhi i)}

end DRAllocCV


