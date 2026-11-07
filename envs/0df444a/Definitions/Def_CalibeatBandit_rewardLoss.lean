-- Prove2me | Definitions.Def_CalibeatBandit_rewardLoss
-- name    : CalibeatBandit_rewardLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:39:27.010202+00:00
-- url     : https://prove2.me/theorems/ae3702f8-4f7e-4c44-87af-8f2dc89b13df
-- title:
--   Reward loss $\mathrm{Rec}_T$ against post-processed recommendations
-- statement:
--   For reward vectors $y_t$, recommended actions $J_t$ (sampled from the recommended mixed strategies $q_t$) and played actions $I_t$, the **reward loss** of the learner against the best post-processing of the recommendation is
--   $$\mathrm{Rec}_T=\max_{\sigma\in\Sigma_{\mathcal A}}\sum_{t=1}^T\bigl(y_t(\sigma(J_t))-y_t(I_t)\bigr).$$
--   It is defined with the *realized* recommended actions $J_t$ of the run, not with a counterfactual run of the recommendation algorithm.
--
--   **Formalization Note** Rounds are $0,\dots,T-1$; the maximum over all maps `Fin K → Fin K` is `Finset.sup'`.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §2.1 (Calibeating), p.8 (PDF 8)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

/-- **Reward loss `Rec_T`** of a realized play against the best post-processing of the
recommended actions: for reward vectors `y_t`, recommended actions `J_t` and played actions
`I_t`,
`Rec_T = max_{σ : 𝒜 → 𝒜} ∑_{t=1}^T (y_t(σ(J_t)) − y_t(I_t))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2.1
"Calibeating", p.8: "For sampled actions {J_t} from recommended mixed strategies {q_t}, Rec_T is
defined similarly to swap regret, with respect to the recommendation algorithm's actions {J_t}."

**Formalization Note.** Rounds are `0, …, T − 1`; the maximum over all maps `Fin K → Fin K` is
`Finset.sup'`. `J` is the *realized* sequence of recommended actions (not a counterfactual
re-run of the recommendation algorithm). -/
def rewardLoss {K : ℕ} (T : ℕ) (y : ℕ → Fin K → ℝ) (J I : ℕ → Fin K) : ℝ :=
  Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
    (fun σ : Fin K → Fin K => ∑ t ∈ Finset.range T, (y t (σ (J t)) - y t (I t)))

end CalibeatBandit


