-- Prove2me | Definitions.Def_RoboAdvising_Sensitivity_optimizer
-- name    : RoboAdvising_Sensitivity_optimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:40:11.15831+00:00
-- url     : https://prove2.me/theorems/0bf8e9c7-c502-4847-88d4-37c5c5237218
-- title:
--   Proposition 5.1(ii) — selection of an actual minimizing interaction interval
-- statement:
--   Let $P=(\sigma_0,p,s,\beta)$ denote the four real parameters of the published interaction model. The objective $\widetilde{\mathcal R}_P$ is the explicit proxy of Proposition 5.1(i), p.21. Define its set of attained minimizers by
--
--   $$
--   M(P)=\{\phi\in[1,\infty):\ \widetilde{\mathcal R}_P(\phi)\le\widetilde{\mathcal R}_P(\psi)\text{ for every real }\psi\ge1\}.
--   $$
--
--   The function $\Phi(P)$ chooses an element of $M(P)$ when this set is nonempty, and returns $1$ otherwise. This is a selection by actual minimization, with no derivative, threshold or uniqueness property inserted into its definition. The goal separately asserts uniqueness and identifies the selected value in every finite regime.
--
--   **Formalization Note** This total, noncomputable function represents the source's uniquely determined finite optimizer when it exists. Its default $1$ is bookkeeping only: at $p=0$, $\beta>0$ there is no finite optimum, so this value has no optimization or sensitivity interpretation. No assertion uses defaults to manufacture derivatives.
-- source:
--   Capponi, Ólafsson, Zariphopoulou, Personalized Robo-Advising: Enhancing Investment through Client Interaction, arXiv:1911.01391v2, pp.21–22, Proposition 5.1(ii), argmin over φ≥1; Appendix C, p.46.

import Mathlib
import Definitions.Def_RoboAdvising_Interaction_Model

namespace RoboAdvising.Sensitivity

/-- The minimizer in Proposition 5.1(ii), arXiv:1911.01391v2, pp. 21–22.
Choose an actual global minimizer over all real interaction intervals at least one,
if one exists. The value is one if no finite minimizer exists. No regularity,
uniqueness, threshold test, or sensitivity is included in this definition.
The corrected goal separately asserts existence and uniqueness in the finite regimes.
At p = 0 and β > 0 the default is not an optimum and has no sensitivity interpretation. -/
noncomputable def optimizer (P : RoboAdvising.Interaction.Params) : ℝ := by
  classical
  exact if h : ∃ φ : ℝ, RoboAdvising.Interaction.IsOptInteraction P φ then
    Classical.choose h
  else 1

end RoboAdvising.Sensitivity


