-- Prove2me | Definitions.Def_CPDETrial_IsNonanticipating
-- name    : CPDETrial_IsNonanticipating
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:53:02.738665+00:00
-- url     : https://prove2.me/theorems/57f930d1-7eb8-4daa-9bb6-68bf591620a4
-- title:
--   Nonanticipating allocation
-- statement:
--   An allocation sequence $(u^t)$ is nonanticipating if each $u^t$ is measurable with respect to the history $\mathcal H_t$ (past allocations and observations together with the external randomization $\mathcal G$): the arm given to patient $t+1$ depends only on what has been observed so far and on independent auxiliary randomness.
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 7 (§1.3, nonanticipating policies)

import Mathlib
import Definitions.Def_CPDETrial_hist
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Nonanticipating allocation.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), §1.3, p. 7: "a nonanticipating policy `π : H_t → M` … maps the history at each time
`t = 0, 1, …` to an action `u^t`".

`IsNonanticipating 𝓖 θ ε u` says that each allocation `u t` is measurable with respect to
`hist 𝓖 θ ε u t`: it depends only on the external randomization and on the allocations and
observations of patients `1, …, t`.

**Formalization Note.** Allowing `u t` to depend on the external randomization `𝓖` covers the
paper's random tie-breaking (p. 11) and random consideration sets (App. B.10). -/
def IsNonanticipating {M : ℕ} {Ω : Type*} (𝓖 : MeasurableSpace Ω)
    (θ : Ω → EuclideanSpace ℝ (Fin M)) (ε : ℕ → Fin M → Ω → ℝ) (u : ℕ → Ω → Fin M) : Prop :=
  ∀ t, Measurable[hist 𝓖 θ ε u t] (u t)

end CPDETrial


