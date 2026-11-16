-- Prove2me | Definitions.Def_MSetBandit_Supplement_runRegret
-- name    : MSetBandit_Supplement_runRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:48:09.011767+00:00
-- url     : https://prove2.me/theorems/957602ef-67e4-4762-99be-7a22ecf97462
-- title:
--   Realized regret $R_T$ of an interaction
-- statement:
--   For a randomized algorithm, a deterministic adversary and a realization $\omega$ of the private randomness, let $X_t(\omega)$ and $\ell_t(\omega)$ be the actions and loss vectors of the interaction. The **realized regret** after $T$ rounds is
--   $$
--   R_T(\omega)=\sum_{t=1}^T X_t(\omega)^\top\ell_t(\omega)-\min_{x\in\mathcal X_{d,m}}\sum_{t=1}^T x^\top\ell_t(\omega),
--   $$
--   the regret (4) of the paper against the best fixed action in hindsight.
--
--   **Formalization Note** It is the base mission's realized regret applied to the action and loss sequences of the run, with rounds indexed from $0$.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, Eq. (4), p.4

import Mathlib
import Definitions.Def_MSetBandit_regret
import Definitions.Def_MSetBandit_Supplement_runHist

namespace MSetBandit.Supplement

/-- **Realized regret of an interaction.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, Eq. (4), p.4:
`R_T := Σ_{t=1}^T X_t^⊤ℓ_t − min_{x∈X} Σ_{t=1}^T x^⊤ℓ_t`, for the interaction of `alg` with
`adv` at the private randomness `ω`: `X_t = h_t(H_{t−1}, ω)` and `ℓ_t = f_t(H_{t−1})` with
`H_{t−1} = runHist alg adv ω t`.

**Formalization Note.** This is the base mission's `MSetBandit.regret` (0-based rounds) applied
to the realized action and loss sequences of the run. -/
noncomputable def runRegret {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (alg : RandAlg d m Ω)
    (adv : DetAdversary d m) (T : ℕ) (ω : Ω) : ℝ :=
  regret T (fun t => adv.f t (runHist alg adv ω t)) (fun t => alg.h t (runHist alg adv ω t) ω)

end MSetBandit.Supplement


