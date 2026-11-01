-- Prove2me | Definitions.Def_SelfGuidedALP_BN
-- name    : SelfGuidedALP_BN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:50.143175+00:00
-- url     : https://prove2.me/theorems/47e26844-916c-4aa5-ace4-ea7220cccad4
-- title:
--   The space $\mathcal B_N$
-- statement:
--   Given samples $\theta^1,\dots,\theta^N$, the paper defines
--   $$
--   \mathcal B_N:=\Bigl\{B:\Theta\to\mathbb R\ \Big|\ \exists(\beta_1,\dots,\beta_N)\in\mathbb R^N,\ \sum_{i=1}^N\beta_i^2<\infty,\ B(\theta)=\sum_{i=1}^N\beta_i\mathbb 1\{\theta=\theta^i\}\Bigr\}.
--   $$
--
--   The orthogonal decomposition of $B^*$ is taken against the closure of this space.
--
--   **Formalization Note** This is the printed definition, inside $\mathcal B$: the span of the classes of the point indicators. A point has Lebesgue measure zero, so these classes vanish and $\mathcal B_N=\{0\}$. The mission's verification file proves this.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition EC.2, p.ec8

import Mathlib
import Definitions.Def_SelfGuidedALP_Bspace

open MeasureTheory

namespace SelfGuidedALP

/-- The space `ℬ_N := {∑_{i=1}^N βᵢ 𝟙{θ = θⁱ}}` of Definition EC.2, as a subspace of `ℬ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition EC.2, p.ec8).

**Formalization Note.** Literally the printed definition: the span in `ℬ` of the classes of the point
indicators `𝟙{θ = θⁱ}`. A point has Lebesgue measure zero, so these classes vanish and `ℬ_N = {0}`;
this is proved in the mission's verification file. -/
noncomputable def BN {d N : ℕ} (R : RBClass d) (θs : Fin N → EuclideanSpace ℝ (Fin (d + 1))) :
    Submodule ℝ (Bspace R) :=
  Submodule.span ℝ
    {B | ∃ i, (B : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =ᵐ[weightMeasure R] Set.indicator {θs i} 1}

end SelfGuidedALP


