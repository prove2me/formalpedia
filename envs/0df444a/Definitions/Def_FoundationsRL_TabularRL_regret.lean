-- Prove2me | Definitions.Def_FoundationsRL_TabularRL_regret
-- name    : FoundationsRL_TabularRL_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:43.724489+00:00
-- url     : https://prove2.me/theorems/2d2f0591-1aea-495f-819b-9570f199a20f
-- title:
--   Regret of a learner over $T$ episodes
-- statement:
--   For an MDP $M$ with initial distribution $d_1$ and a history-dependent learner playing the policy $\widehat\pi^t$ in episode $t$, the **regret** over $T$ episodes is
--
--   $$
--   \mathrm{Reg}=\sum_{t=1}^T f^M(\pi_M)-f^M(\widehat\pi^t),\qquad f^M(\pi)=\mathbb E_{s\sim d_1}V^{M,\pi}_1(s),
--   $$
--
--   where $f^M(\pi_M)=\mathbb E_{s\sim d_1}V^{M,\star}_1(s)$ is the optimal value. It is a function of the realized history of the $T$ episodes, since $\widehat\pi^t$ depends on the first $t-1$ trajectories.
--
--   This is the quantity bounded in Theorem 1.
--
--   **Formalization Note** The regret is the pseudo-regret of the played policies (expected values, not realized rewards). Episodes and layers are $0$-indexed.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §5.6.1, p. 90 (regret display); Eq. (5.1), p. 81; Eq. (5.3), p. 82

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI_v2

namespace FoundationsRL.TabularRL

open FoundationsRL.RLBasics

/-- The regret of a history-dependent learner over `T` episodes (Foster & Rakhlin, *Foundations
of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §5.6.1, p. 90):
`Reg = ∑_{t=1}^T f^M(π_M) − f^M(π̂^t)`, where `f^M(π) = E_{s∼d1} V^{M,π}_1(s)` is the value of a
policy (5.1), `f^M(π_M) = E_{s∼d1} V^{M,⋆}_1(s)` the optimal value (Proposition 25), and `π̂^t`
the policy the learner plays in episode `t`, computed from the first `t − 1` trajectories of the
realized history `histT`.

**Formalization Note.** This is the pseudo-regret of the played policies (expected values, not
realized rewards), a function of the realized `T`-episode history. Episodes are `0`-indexed:
round `t : Fin T` uses `(List.ofFn histT).take t`. Layers are `0`-indexed (`V M π 0` is the
book's `V_1`). -/
noncomputable def regret {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
    {H : ℕ} (M : EpisodicMDP S A H) (learner : Learner S A H) (T : ℕ)
    (histT : Fin T → Trajectory S A H) : ℝ :=
  ∑ t : Fin T,
    ((∑ s : S, M.d1 s * Vstar M 0 s) -
      ∑ s : S, M.d1 s * V M (learner ((List.ofFn histT).take t.1)) 0 s)

end FoundationsRL.TabularRL


