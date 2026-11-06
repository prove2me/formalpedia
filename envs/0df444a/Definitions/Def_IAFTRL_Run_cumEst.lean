-- Prove2me | Definitions.Def_IAFTRL_Run_cumEst
-- name    : IAFTRL_Run_cumEst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:34.255131+00:00
-- url     : https://prove2.me/theorems/cd5814d7-eb1c-420f-bb04-6bd440fc92cd
-- title:
--   Cumulative estimate $\sum_{s<t}\hat\theta_s$
-- statement:
--   The **cumulative estimate** before round $t$ is
--   $$
--   S_{t}=\sum_{s<t}\hat\theta_s ,
--   $$
--   with $S_0=0$. The cumulative estimated loss of action $a$ is $\hat L_{a}=a^\top S_t$ (Algorithm 1, lines 1 and 8). Every quantity IA-FTRL computes in a round depends only on $\mathcal A$, the round index and this vector.
--
--   **Formalization Note** Rounds are 0-based: the Lean vector at round $t$ is the paper's $\sum_{s=1}^{t}\hat\theta_s$, used in its round $t+1$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Algorithm 1, lines 1 and 8, p.18; p.56

import Mathlib
import Definitions.Def_IAFTRL_Run_thetaHat

namespace IAFTRL

/-- **The cumulative estimate `Σ_{s<t} θ̂_s`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Algorithm 1, lines 1 and 8, p.18:
"Set `L̂_{0,a} = 0`" and "Update `L̂_{t,a} = L̂_{t−1,a} + ℓ̂_{t,a}`", with `ℓ̂_{t,a} = a^⊤θ̂_t`; p.56:
"All quantities in the algorithm depend only on `𝒜, t, Σ_{s=1}^{t−1} θ̂_s`".

`R.cumEst arms t ω = Σ_{s<t} θ̂_s` (0-based), so `⟨a, R.cumEst arms t ω⟩` is the cumulative estimated
loss of `a` before (0-based) round `t`, i.e. the paper's `L̂_{t,a}` used in its round `t + 1`. -/
noncomputable def Run.cumEst {d K : ℕ} {Ω : Type*} (R : Run d K Ω)
    (arms : Fin K → Fin d → ℝ) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  ∑ s ∈ Finset.range t, R.thetaHat arms s ω

end IAFTRL


