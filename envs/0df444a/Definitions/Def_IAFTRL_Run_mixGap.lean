-- Prove2me | Definitions.Def_IAFTRL_Run_mixGap
-- name    : IAFTRL_Run_mixGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:49:48.654328+00:00
-- url     : https://prove2.me/theorems/23186611-cfd3-46fb-b6aa-74e058d26ced
-- title:
--   Mixability gap $D_t$
-- statement:
--   In round $t$ the **entropy-FTRL mixability gap** is
--   $$
--   D_t=\langle q_t,g_t\rangle+\beta_t\log\sum_{a}q_{t,a}\,e^{-g_{t,a}/\beta_t},
--   $$
--   with the exponential weights $q_t$, the scale $\beta_t$ and the estimated loss differences $g_{t,a}$. It is the one-round stability term in the FTRL regret bound of Lemma J.2.
--
--   **Formalization Note** The Lean round $t$ is the paper's round $t+1$ and uses $\beta_{t+1}$ and $q_{t+1}$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Lemma J.2, p.205; Lemma D.4, p.70

import Mathlib
import Definitions.Def_IAFTRL_Run_gEst
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_qSoft

namespace IAFTRL

/-- **The entropy-FTRL mixability gap `D_t`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma J.2, p.205: "`D_t = ⟨q_t, g_t⟩ +
β_t log Σ_a q_{t,a} e^{−g_{t,a}/β_t}`"; used with `g_{t,a} = (a − r_t)^⊤v_{t,A_t}Y_t` in Lemma D.4, p.70.

`R.mixGap arms t ω = Σ_a q_{t,a} g_{t,a} + β_t log Σ_a q_{t,a} exp(−g_{t,a}/β_t)` with
`β_t = beta d K (t+1)` and `q_t = qSoft β_t arms (Σ_{s<t} θ̂_s)` (0-based round `t`, paper round
`t + 1`). -/
noncomputable def Run.mixGap {d K : ℕ} {Ω : Type*} (R : Run d K Ω)
    (arms : Fin K → Fin d → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a * R.gEst arms t a ω +
    beta d K (t + 1) * Real.log (∑ a, qSoft (beta d K (t + 1)) arms (R.cumEst arms t ω) a *
      Real.exp (-(R.gEst arms t a ω) / beta d K (t + 1)))

end IAFTRL


