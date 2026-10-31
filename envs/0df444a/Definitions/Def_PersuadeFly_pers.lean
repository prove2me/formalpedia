-- Prove2me | Definitions.Def_PersuadeFly_pers
-- name    : PersuadeFly_pers
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:29:09.706535+00:00
-- url     : https://prove2.me/theorems/ef3cc1b2-32c8-4970-89db-ef3067bb2939
-- title:
--   Persuasive mechanisms $\mathsf{Pers}(\mu)$, (1)
-- statement:
--   For a distribution $\mu$ on $\Omega$, the set of **persuasive mechanisms** is
--   $$
--   \mathsf{Pers}(\mu)=\Big\{\sigma\in\mathcal S:\ \sum_{\omega\in\Omega}\mu(\omega)\,\sigma(\omega,a)\,\big(u(\omega,a)-u(\omega,a')\big)\ge0\ \text{ for all }a,a'\in A\Big\}.
--   $$
--   Under $\sigma\in\mathsf{Pers}(\mu)$ a receiver with prior $\mu$ who is recommended $a$ finds $a$ optimal.
--
--   **Formalization Note** The constraint is the unnormalized form (1) of the paper, which holds trivially for an action recommended with probability $0$.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §2.1, eq. (1), p.14

import Mathlib
import Definitions.Def_PersuadeFly_Instance
import Definitions.Def_PersuadeFly_IsMechanism

namespace PersuadeFly

/-- **Persuasive mechanisms `Pers(μ)`**, (1). Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §2.1, eq. (1), p.14:
`Pers(μ) = {σ ∈ S : ∑_ω μ(ω) σ(ω, a) (u(ω, a) − u(ω, a')) ≥ 0 for all a, a' ∈ A}`.

**Formalization Note** The obedience constraint is the unnormalized form (1), as printed; it is
trivially satisfied by an action recommended with probability 0. -/
def pers {Ω A : Type} [Fintype Ω] [Fintype A] (I : Instance Ω A) (μ : Ω → ℝ) : Set (Ω → A → ℝ) :=
  {σ | IsMechanism σ ∧ ∀ a a' : A, 0 ≤ ∑ ω, μ ω * σ ω a * (I.u ω a - I.u ω a')}

end PersuadeFly


