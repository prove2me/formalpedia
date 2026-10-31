-- Prove2me | Definitions.Def_PersuadeFly_gap
-- name    : PersuadeFly_gap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:58.950627+00:00
-- url     : https://prove2.me/theorems/b1c9da05-5cef-40b9-a722-ce64da46778c
-- title:
--   The cost of robust persuasion $\mathsf{Gap}(\mu,\mathcal B)$, (4)
-- statement:
--   The **cost of robust persuasion** of a set $\mathcal B$ at $\mu$:
--   $$
--   \mathsf{Gap}(\mu,\mathcal B)=\sup_{\sigma\in\mathsf{Pers}(\mu)}V(\mu,\sigma)-\sup_{\sigma\in\mathsf{Pers}(\mathcal B)}V(\mu,\sigma).
--   $$
--   It is the loss in expected utility, under $\mu$, from requiring the mechanism to be persuasive for every distribution in $\mathcal B$.
--
--   **Formalization Note** For $\mathcal B\subseteq\Delta(\Omega)$ both suprema are over nonempty sets on which $V(\mu,\cdot)$ is bounded: the full-information mechanism is persuasive under every prior.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §4, eq. (4), p.23

import Mathlib
import Definitions.Def_PersuadeFly_opt
import Definitions.Def_PersuadeFly_persSet

namespace PersuadeFly

/-- **The cost of robust persuasion `Gap(μ, B)`**, (4). Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §4, eq. (4), p.23:
`Gap(μ, B) = sup_{σ ∈ Pers(μ)} V(μ, σ) − sup_{σ ∈ Pers(B)} V(μ, σ)`.

**Formalization Note** Both suprema are real `sSup`s over sets of mechanisms. For `B ⊆ Δ(Ω)` the set
`Pers(B)` contains the full-information mechanism, and `V(μ, ·)` is bounded on mechanisms, so both
suprema are of nonempty bounded sets. -/
noncomputable def gap {Ω A : Type} [Fintype Ω] [Fintype A] (I : Instance Ω A) (μ : Ω → ℝ)
    (B : Set (Ω → ℝ)) : ℝ :=
  opt I μ - sSup (value I μ '' persSet I B)

end PersuadeFly


