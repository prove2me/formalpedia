-- Prove2me | Definitions.Def_FoundationsRL_DECLower_expRegret
-- name    : FoundationsRL_DECLower_expRegret
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:11:08.223751+00:00
-- url     : https://prove2.me/theorems/a45318a2-1c1e-4c59-bbf6-0dad8cab2936
-- title:
--   Expected regret $\mathbb E_{M,p}[\mathrm{Reg}(T)]$
-- statement:
--   For an algorithm $p$, a model $M$ and a horizon $T$, the **expected regret** is
--
--   $$
--   \mathbb E_{M,p}[\mathrm{Reg}(T)]=\mathbb E_{H_T\sim\mathbb P^M}\left[\sum_{t=1}^T\mathbb E_{\pi_t\sim p_t(\cdot\mid H_{t-1})}\bigl[f^M(\pi_M)-f^M(\pi_t)\bigr]\right],
--   $$
--
--   the regret (6.3) to the optimal decision of the true model, in expectation over the interaction (footnote 14).
--
--   This is the quantity Proposition 28 bounds from below.
--
--   **Formalization Note** The inner expectation is over $\pi_t\sim p_t$ given the realized history, as in (6.3); rounds are $0$-based in Lean. For a model the integrand lies in $[0,T]$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, (6.3), p. 94; (6.27) and footnote 14, p. 104

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_gap
import Definitions.Def_FoundationsRL_DECLower_Algorithm_policyAt
import Definitions.Def_FoundationsRL_DECLower_histLaw

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Expected regret** `E_{M,p}[Reg(T)]`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, (6.3), p. 94 ("Reg := Σ_{t=1}^T E_{π_t∼p_t}[f^{M⋆}(π_{M⋆}) − f^{M⋆}(π_t)]") and (6.27) with
footnote 14, p. 104 (expectation over the observation process and the algorithm's randomization).

`expRegret alg M T = E_{H_T ∼ P^M}[Σ_{t=1}^T E_{π∼p_t(·|H_{t−1})}[f^M(π_M) − f^M(π)]]`.

**Formalization Note.** (6.3) literally: the inner expectation is over `π_t ∼ p_t` (the decision
distribution at round `t` given the realized history), the outer over the history law. 0-based:
`t : Fin T` is round `t + 1`. For a model the integrand is bounded in `[0, T]`. -/
noncomputable def expRegret {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (alg : Algorithm D O) (M : Kernel D (ℝ × O)) (T : ℕ) : ℝ :=
  ∫ h, ∑ t : Fin T, ∫ d, gap M d ∂(alg.policyAt T t h) ∂(histLaw alg M T)

end FoundationsRL.DECLower


