-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_IsUniformlyIntegrable
-- name    : ProcessingNetworks_MArP_IsUniformlyIntegrable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:23.283771+00:00
-- url     : https://prove2.me/theorems/40b7b3a5-31a6-40d5-b328-5d5d60e840be
-- title:
--   Uniform integrability of a family of random variables (Definition B.1)
-- statement:
--   A family of real random variables $\{X_i : i\in\iota\}$ on a probability space is **uniformly integrable** if
--   $$
--   \lim_{a\to\infty}\ \sup_{i\in\iota}\ \mathbb E\big(|X_i|\,1_{\{|X_i|>a\}}\big)=0 .
--   $$
--
--   The book states this for a sequence and then applies it to the family indexed by the real numbers $t\ge 1$, so the index set here is arbitrary. Uniform integrability is what upgrades almost-sure convergence of fluid-scaled processes to convergence of their means.
--
--   **Formalization Note** Expectations are Lebesgue integrals with values in $[0,\infty]$, and the supremum is taken there, so no junk value arises. Each $X_i$ is required to be almost-everywhere measurable, which is the meaning of "random variable" and is needed because the Lebesgue integral of a non-measurable function is only a lower integral.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition B.1, eq. (B.1), p.265 (PDF p.281)

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ProcessingNetworks.MArP

/-- Uniform integrability of a family of random variables (Dai & Harrison, Processing Networks,
pre-publication draft 2020-4-2, Definition B.1, eq. (B.1), p.265, PDF p.281):
`lim_{a → ∞} sup_{i} E(|X_i| 1{|X_i| > a}) = 0`.

**Formalization Note.** The book writes (B.1) for a sequence; Proposition B.5 and Proposition E.7(b)
apply it to the family indexed by the real numbers `t ≥ 1`, so the index type `ι` is arbitrary.
Expectations are `ℝ≥0∞`-valued Lebesgue integrals, so there is no junk value for a non-integrable
variable, and the supremum is taken in the complete lattice `ℝ≥0∞`. "Random variable" is carried as
`AEMeasurable`, because a Lebesgue integral of a non-measurable function is only a lower integral. -/
def IsUniformlyIntegrable {ι Ω : Type*} [MeasureSpace Ω] (X : ι → Ω → ℝ) : Prop :=
  (∀ i, AEMeasurable (X i) ℙ) ∧
    Tendsto
      (fun a : ℝ => ⨆ i, ∫⁻ ω, Set.indicator {ω | a < |X i ω|} (fun ω => ‖X i ω‖ₑ) ω)
      atTop (nhds 0)

end ProcessingNetworks.MArP


