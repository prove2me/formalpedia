-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_regret
-- name    : FoundationsRL_LinUCB_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:11.181578+00:00
-- url     : https://prove2.me/theorems/cc0baa64-0c39-4a02-bb90-e9af92128158
-- title:
--   Regret $\mathrm{Reg}$ of a contextual bandit run (Eq. (3.3))
-- statement:
--   The **regret** of a run over $T$ rounds is the random variable
--
--   $$
--   \mathrm{Reg}=\sum_{t=1}^T f^\star\bigl(x^t,\pi^\star(x^t)\bigr)-\sum_{t=1}^T\mathbb E_{\pi^t\sim p^t}\bigl[f^\star(x^t,\pi^t)\bigr],
--   $$
--
--   where $\pi^\star(x)$ maximizes $f^\star(x,\cdot)$ and $p^t$ is the learner's action distribution at round $t$. The benchmark is the best action for each context, not the best single action.
--
--   **Formalization Note** The term $f^\star(x,\pi^\star(x))$ is written $\sup_\pi f^\star(x,\pi)$, its value, so no maximizer needs to exist. With rewards in $[0,1]$ the supremum is over a bounded nonempty set.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (3.3), p. 39

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_ContextualBanditRun
import Definitions.Def_FoundationsRL_LinUCB_meanReward

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- The regret of a run over `T` rounds (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.3), p. 39):
`Reg = ∑_{t=1}^T f⋆(x^t, π⋆(x^t)) − ∑_{t=1}^T E_{π^t∼p^t}[f⋆(x^t, π^t)]`, a random variable.

**Formalization Note.** `f⋆(x, π⋆(x))` is written `⨆ a, f⋆(x, a)`, the value of the book's
`arg max`, so no maximizer needs to exist. With rewards in `[0, 1]` the supremum is over a
bounded nonempty set and is not a junk value. The inner expectation is the Bochner integral
against `p^t`, not the realized reward. -/
noncomputable def regret {Ω X Act : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
    [MeasurableSpace Act] {P : Measure Ω} {Mstar : Kernel (X × Act) ℝ}
    (R : ContextualBanditRun P Mstar) (T : ℕ) (ω : Ω) : ℝ :=
  (∑ t ∈ Finset.range T, ⨆ a : Act, meanReward Mstar (R.x t ω) a) -
    ∑ t ∈ Finset.range T, ∫ a, meanReward Mstar (R.x t ω) a ∂(R.p t ω)

end FoundationsRL.LinUCB


