-- Prove2me | Definitions.Def_DataValidation_value
-- name    : DataValidation_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:48:57.681932+00:00
-- url     : https://prove2.me/theorems/7a7e70d8-1979-49be-87c5-3831994f90df
-- title:
--   The optimal value of a DVP instance
-- statement:
--   A **randomized policy** is a probability space of seeds $\xi$, independent of $\{\Omega_e\}$, with a valid deterministic policy $\pi_\xi$ for each seed, such that $\xi\mapsto W(\pi_\xi)$ is integrable; its reward is $\int W(\pi_\xi)\,d\mu(\xi)$. The **optimal value** of an instance $I$ is
--
--   $$\operatorname{value}(I)=\sup\Big\{\int W(\pi_\xi)\,d\mu(\xi) : (\pi_\xi)\text{ a valid randomized policy}\Big\}.$$
--
--   This is the objective $\max_\pi W(\pi)$ of the paper, in which policies may sample random variables independent of $\{\Omega_e\}$. On a valid instance the set is nonempty and bounded above by $\sum_{e\in E}w_e$.
--
--   **Formalization Note** A policy that samples adaptively is of this form, since the seed can hold all its random draws in advance.
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), §1, p.1

import Definitions.Def_DataValidation_Policy

set_option autoImplicit false

namespace DataValidation

open MeasureTheory

/-- `r` is the expected reward of some **valid randomized policy**: a probability space of seeds `ξ`,
independent of `{Ω_e}`, and for each seed a valid deterministic policy, with reward
`∫ W(π_ξ) dμ(ξ)`. arXiv:2611.06773 (sha256 6595f819…), §1, p.1: "we allow policies to sample random
variables other than {Ω_e}_{e∈E} but that are independent of {Ω_e}_{e∈E}".

**Formalization Note.** A policy that samples adaptively is of this form: the seed holds all its random
draws in advance. Taking `π` to be constant gives the deterministic policies. Integrability of
`ξ ↦ W(π_ξ)` is required, since a Bochner integral of a non-integrable function is `0`. -/
def Instance.IsPolicyReward (I : Instance) (r : ℝ) : Prop :=
  ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (μ : Measure Ξ) (_ : IsProbabilityMeasure μ)
    (π : Ξ → I.Policy),
    (∀ ξ, Instance.IsValidPolicy (π ξ)) ∧
    Integrable (fun ξ => Instance.W (π ξ)) μ ∧
    r = ∫ ξ, Instance.W (π ξ) ∂μ

/-- The **optimal value** of a DVP instance, `sup_π W(π)` over all valid policies, randomized ones
included: the objective `max_{policy π} W(π)` of arXiv:2611.06773 (sha256 6595f819…), §1, p.1.

**Formalization Note.** On a valid instance the set is nonempty (the policy that stops at once) and
bounded above by `∑_{e∈E} w_e`, so this real supremum is a true one. It is not defined through
obtainable sets; `DataValidation.value_eq_max_obtainable` is the bridge at `p ≡ 1`. -/
noncomputable def Instance.value (I : Instance) : ℝ :=
  sSup {r : ℝ | I.IsPolicyReward r}

end DataValidation


