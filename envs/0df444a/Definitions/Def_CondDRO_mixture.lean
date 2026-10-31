-- Prove2me | Definitions.Def_CondDRO_mixture
-- name    : CondDRO_mixture
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:17.602583+00:00
-- url     : https://prove2.me/theorems/58544efb-e6e2-476f-be98-fc4010ee3ae3
-- title:
--   Mixture $\mathfrak M_\nu=\sum_{i\in\mathcal I}\nu_i\mathfrak A_i$ of atom-wise sets, display (2.9)
-- statement:
--   Let $\mathcal I$ be a finite index set, $\mathfrak A_i$ ($i\in\mathcal I$) sets of measures on a measurable space $(\Omega,\mathcal F)$, and $\nu=(\nu_i)_{i\in\mathcal I}$ weights (in the paper: positive probabilities, $\nu_i>0$, $\sum_i\nu_i=1$). The **mixture** of the sets $\mathfrak A_i$ with weights $\nu$ is the Minkowski combination
--
--   $$
--   \mathfrak M_\nu:=\sum_{i\in\mathcal I}\nu_i\,\mathfrak A_i=\Bigl\{\,Q=\sum_{i\in\mathcal I}\nu_iQ_i\ :\ Q_i\in\mathfrak A_i,\ i\in\mathcal I\Bigr\}.
--   $$
--
--   When each $\mathfrak A_i$ consists of probability measures supported on the atom $\varpi_i$ of a partition, $\mathfrak M_\nu$ is an ambiguity set on $\Omega$ whose members put mass $\nu_i$ on $\varpi_i$; it is the set through which Proposition 2.1 identifies the conditional risk measure (2.7) with a conditional distributionally robust functional (2.6).
--
--   **Formalization Note** The weights are real numbers $\nu_i$, entering the sum of measures as the nonnegative scalars $\max(\nu_i,0)$ (`ENNReal.ofReal`); under the hypothesis $\nu_i>0$ of the theorems this is $\nu_i$. The conditions $\nu_i>0$ and $\sum_i\nu_i=1$ are hypotheses of the theorems, not part of the definition.
-- source:
--   Shapiro & Pichler, Conditional Distributionally Robust Functionals, preprint (October 9, 2022), display (2.9), p.5; written out in Example 2.1, p.7

import Mathlib

open MeasureTheory

namespace CondDRO

/-- **The mixture 𝔐_ν = Σᵢ νᵢ 𝔄ᵢ of sets of measures** (Shapiro & Pichler, *Conditional
Distributionally Robust Functionals*, preprint (October 9, 2022), display (2.9), p.5; written out in
Example 2.1, p.7, as `𝔐_ν = { Q = Σ_{i∈ℐ} νᵢ Qᵢ | Qᵢ ∈ 𝔄ᵢ, i ∈ ℐ }`): the set of all measures
`Σᵢ νᵢ Qᵢ` with `Qᵢ ∈ 𝔄ᵢ` for every `i`.

**Formalization Note.** The index set `I` is finite (`[Fintype I]`). The weights are real numbers
`ν i`, entering the sum of measures as the nonnegative scalars `ENNReal.ofReal (ν i)`; the
requirements `νᵢ > 0`, `Σ νᵢ = 1` of (2.9) are hypotheses of the theorems using this set. -/
noncomputable def mixture {Ω : Type*} [MeasurableSpace Ω] {I : Type*} [Fintype I]
    (A : I → Set (Measure Ω)) (ν : I → ℝ) : Set (Measure Ω) :=
  {Q : Measure Ω | ∃ q : I → Measure Ω, (∀ i, q i ∈ A i) ∧ Q = ∑ i, ENNReal.ofReal (ν i) • q i}

end CondDRO


