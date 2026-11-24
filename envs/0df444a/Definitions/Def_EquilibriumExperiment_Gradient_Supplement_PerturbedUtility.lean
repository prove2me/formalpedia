-- Prove2me | Definitions.Def_EquilibriumExperiment_Gradient_Supplement_PerturbedUtility
-- name    : EquilibriumExperiment_Gradient_Supplement_PerturbedUtility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:18:16.366826+00:00
-- url     : https://prove2.me/theorems/a828efad-700c-4400-8fb5-7046105f0864
-- title:
--   §4.3 — positive perturbed mean-field equilibrium and utility with payment–activation correlation
-- statement:
--   For a published market $M$, write $d$ for limiting demand, $\beta$ for the feature law, $f_b$ for choice probabilities, $\omega$ for the regular allocation function and $r$ for limiting revenue per active supplier. Let $P=p+\zeta\varepsilon$, with equiprobable signs independent of $B\sim\beta$. Define $\mu_\zeta$ to be the positive equilibrium root and set
--   $$\mu_\zeta=\mathbb E[f_B(P\omega(d/\mu_\zeta))],\qquad q_\zeta=\omega(d/\mu_\zeta),\qquad u(p,\zeta)=r(d/\mu_\zeta)\mu_\zeta-q_\zeta\mathbb E[P f_B(Pq_\zeta)].$$
--   This is the mean-field utility of the symmetric payment law in (3.8)–(3.11). The expectation retains the correlation between payment and activation. The matching rate and active fraction are both evaluated at the perturbed equilibrium. At zero perturbation uniqueness of the positive root gives $\mu_0=\mu(p)$ and $u(p,0)=u(p)$, the published unperturbed utility.
--
--   **Formalization Note** Roots are selected from $(0,1]$. The fallback value zero is outside the positive-payment, activation-positivity regime of the theorem. On that regime bounded measurable choice functions make both expectations integrable. No finite-market revenue function or realized service is added: the identification with limiting expected utility is derived from (3.3), (3.6), (3.8)–(3.10) and Assumptions 1–3 in MODERATION_NOTES.md. The definitions contain no cost bound.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, pp. 16–18, (3.6), (3.8)–(3.15); p. 23, (4.8); p. 40, Appendix A.7

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

namespace EquilibriumExperiment.Gradient.Supplement

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

/-- Mean-field balance map for the actual symmetric payment law (3.6), (3.11), (A.2). -/
noncomputable def psiPert {B : Type} [MeasurableSpace B] (M : Market B)
    (p ζ μ : ℝ) : ℝ :=
  ∫ b, ∫ P, M.f b (P * M.ω (M.d / μ)) ∂(perturbLaw p ζ) ∂M.β

/-- The actual positive perturbed mean-field equilibrium root. The off-domain default
0 is never used under the positive-payment and activation-positivity hypotheses. -/
noncomputable def muPert {B : Type} [MeasurableSpace B] (M : Market B)
    (p ζ : ℝ) : ℝ :=
  if h : ∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ = psiPert M p ζ μ then h.choose else 0

/-- Mean-field service per active supplier, evaluated at the perturbed equilibrium. -/
noncomputable def qPert {B : Type} [MeasurableSpace B] (M : Market B)
    (p ζ : ℝ) : ℝ := M.ω (M.d / muPert M p ζ)

/-- Mean-field utility at symmetric perturbation ζ, from (3.8)–(3.11), (3.15).
The payment P remains correlated with activation f_B(P q); it is NOT replaced by p μ. -/
noncomputable def uPert {B : Type} [MeasurableSpace B] (M : Market B)
    (p ζ : ℝ) : ℝ :=
  M.r (M.d / muPert M p ζ) * muPert M p ζ -
    qPert M p ζ * (∫ b, ∫ P, P * M.f b (P * qPert M p ζ)
      ∂(perturbLaw p ζ) ∂M.β)

end EquilibriumExperiment.Gradient.Supplement


