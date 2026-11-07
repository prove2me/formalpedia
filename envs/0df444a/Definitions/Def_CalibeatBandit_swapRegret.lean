-- Prove2me | Definitions.Def_CalibeatBandit_swapRegret
-- name    : CalibeatBandit_swapRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:29.528645+00:00
-- url     : https://prove2.me/theorems/0c18727d-5842-424b-8039-9da05bd8c779
-- title:
--   Swap regret $\mathrm{SR}_T$ of a realized play
-- statement:
--   Let $\Sigma_{\mathcal A}$ be the set of all maps $\sigma:\mathcal A\to\mathcal A$ (post-processing maps). For reward vectors $y_1,\dots,y_T\in\mathbb R^K$ and played actions $I_1,\dots,I_T$, the learner's cumulative **swap regret** is the best improvement obtained by post-processing the learner's actions in hindsight:
--   $$\mathrm{SR}_T=\max_{\sigma\in\Sigma_{\mathcal A}}\sum_{t=1}^T\bigl(y_t(\sigma(I_t))-y_t(I_t)\bigr).$$
--   In the interaction protocol $y_t$ and $I_t$ are random, so $\mathrm{SR}_T$ is a random variable.
--
--   **Formalization Note** Rounds are $0,\dots,T-1$; the maximum over the finite nonempty set of maps `Fin K → Fin K` is `Finset.sup'`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §2.1 (Calibeating), p.8 (PDF 8)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

/-- **Swap regret `SR_T`** of a realized play: for reward vectors `y_t ∈ ℝ^K` and played actions
`I_t`,
`SR_T = max_{σ : 𝒜 → 𝒜} ∑_{t=1}^T (y_t(σ(I_t)) − y_t(I_t))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2.1
"Calibeating", p.8: "Let Σ_𝒜 be the set of all post-processing maps from one action to another
action σ : 𝒜 ⟶ 𝒜. The learner's cumulative swap regret SR_T is the best improvement obtained by
post-processing the learner's actions, chosen in hindsight".

**Formalization Note.** Rounds are indexed `0, …, T − 1` (`Finset.range T`) instead of
`1, …, T`; actions are `Fin K`. The maximum over the finite, nonempty set of all maps
`Fin K → Fin K` (it contains `id`) is `Finset.sup'`. In the protocol `SR_T` is a random variable:
`y` and `I` are the realized sequences. -/
def swapRegret {K : ℕ} (T : ℕ) (y : ℕ → Fin K → ℝ) (I : ℕ → Fin K) : ℝ :=
  Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
    (fun σ : Fin K → Fin K => ∑ t ∈ Finset.range T, (y t (σ (I t)) - y t (I t)))

end CalibeatBandit


