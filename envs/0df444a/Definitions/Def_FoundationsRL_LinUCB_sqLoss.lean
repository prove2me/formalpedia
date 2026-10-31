-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_sqLoss
-- name    : FoundationsRL_LinUCB_sqLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:29.967061+00:00
-- url     : https://prove2.me/theorems/58fdc060-3733-49df-8180-73541793fd6d
-- title:
--   Empirical square loss on the data before round $t$
-- statement:
--   The **empirical square loss** of $f:\mathcal X\times\Pi\to\mathbb R$ on the data observed before round $t$ of a run is
--
--   $$
--   \sum_{i<t}\bigl(f(x^i,\pi^i)-r^i\bigr)^2.
--   $$
--
--   It is the objective of the least-squares estimators of §3.1 and of the LinUCB algorithm.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eq. (3.8), p. 41

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_ContextualBanditRun

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- The empirical square loss `∑_{i<t} (f(x^i, π^i) − r^i)²` of `f` on the data of the rounds
before round `t` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.8), p. 41). -/
def sqLoss {Ω X Act : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
    [MeasurableSpace Act] {P : Measure Ω} {Mstar : Kernel (X × Act) ℝ}
    (R : ContextualBanditRun P Mstar) (f : X → Act → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range t, (f (R.x i ω) (R.act i ω) - R.r i ω) ^ 2

end FoundationsRL.LinUCB


