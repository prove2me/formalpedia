-- Prove2me | Definitions.Def_OfflineToOnline_onlineIG
-- name    : OfflineToOnline_onlineIG
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:06.47279+00:00
-- url     : https://prove2.me/theorems/96828dc3-7e97-4930-915b-360aa26659f0
-- title:
--   Online-IG, the full-information online meta-algorithm (Algorithm 2)
-- statement:
--   Given an instance of Algorithm 1 and a payoff-based Blackwell algorithm $\mathrm{AlgB}$, **Online-IG** runs $N$ parallel copies $\mathrm{AlgB}^{(1)},\dots,\mathrm{AlgB}^{(N)}$ of $\mathrm{AlgB}$ against an oblivious sequence $f_1,\dots,f_T\in\mathcal F$. In round $t$ it starts from $z_t^{(0)}=z^{(0)}$ and, for $i=1,\dots,N$, sets
--
--   $$
--   \theta_t^{(i)}=\mathrm{AlgB}^{(i)}\Big(\theta_1^{(i)},\dots,\theta_{t-1}^{(i)},\ \textsc{Payoff}\big(\theta_1^{(i)},z_1^{(i-1)},f_1\big),\dots,\textsc{Payoff}\big(\theta_{t-1}^{(i)},z_{t-1}^{(i-1)},f_{t-1}\big)\Big),\qquad z_t^{(i)}=\textsc{Local-update}\big(\theta_t^{(i)},z_t^{(i-1)}\big),
--   $$
--
--   and plays $z_t=z_t^{(N)}$. The feedback $\textsc{Payoff}(\theta_t^{(i)},z_t^{(i-1)},f_t)$ is the vector payoff $\boldsymbol p(\theta_t^{(i)},y_t^{(i)})$ of copy $i$ against the implicit player 2 action $y_t^{(i)}=\mathrm{AdvB}(z_t^{(i-1)},f_t)$.
--
--   The definition gives Online-IG as a parameter policy: its value at round $t$, subproblem $i$ and seed realization $\omega$ is $\theta_t^{(i)}$, and the played points are the run points of that policy.
--
--   **Formalization Note** Rounds and subproblems are $0$-indexed; round $t$ uses only $f_s$ with $s<t$. The parameters are computed by well-founded recursion on the round (`onlineIGParams`).
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Algorithm 2, p.21

import Mathlib
import Definitions.Def_OfflineToOnline_IGInstance
import Definitions.Def_OfflineToOnline_runPoints
import Definitions.Def_OfflineToOnline_payoffPlay

namespace OfflineToOnline

/-- The parameters chosen by Online-IG (Algorithm 2, p.21) on the seed realization `ω`:
`θ_t^(i) = AlgB^(i)(θ_1^(i), …, θ_{t−1}^(i), Payoff(θ_1^(i), z_1^(i−1), f_1), …,
Payoff(θ_{t−1}^(i), z_{t−1}^(i−1), f_{t−1}))`, where every `AlgB^(i)` is a copy of the same
payoff-based strategy `A`, and `z_s^(i−1)` is computed from round `s`'s parameters by
`roundPoints`. -/
noncomputable def onlineIGParams {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω] {m d : ℕ}
    (I : IGInstance D Ω m d) (A : PayoffStrategy m d) {T : ℕ} (f : Fin T → D → ℝ)
    (ω : Fin T → Fin I.N → Ω) : Fin T → Fin I.N → Fin m → ℝ
  | t, i => A t.1 (fun s =>
      (onlineIGParams I A f ω ⟨s.1, s.2.trans t.2⟩ i,
        I.payoff (onlineIGParams I A f ω ⟨s.1, s.2.trans t.2⟩ i)
          (roundPoints I (fun j => onlineIGParams I A f ω ⟨s.1, s.2.trans t.2⟩ j)
            (ω ⟨s.1, s.2.trans t.2⟩) i)
          (f ⟨s.1, s.2.trans t.2⟩)))
termination_by t => t.1
decreasing_by all_goals exact s.2

/-- Online-IG, Algorithm 2, p.21, as a parameter policy: `onlineIG I A f t i ω` is `θ_t^(i+1)`
on the seed realization `ω`, with `N` parallel copies of the Blackwell algorithm `A` fed the
realized vector payoffs `p(θ_s^(i), y_s^(i)) = Payoff(θ_s^(i), z_s^(i−1), f_s)` of earlier rounds.
The played points are `z_t = runPoints I (onlineIG I A f) t N ω` and `z_t^(0) = z₀` in every round.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Algorithm 2, p.21.

Formalization Note: rounds and subproblems are `0`-indexed. `f` is the oblivious adversary's
sequence `f_1, …, f_T`, fixed in advance; round `t` uses only `f_s` for `s < t`. -/
noncomputable def onlineIG {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω] {m d : ℕ}
    (I : IGInstance D Ω m d) (A : PayoffStrategy m d) {T : ℕ} (f : Fin T → D → ℝ) :
    Fin T → Fin I.N → (Fin T → Fin I.N → Ω) → Fin m → ℝ :=
  fun t i ω => onlineIGParams I A f ω t i

end OfflineToOnline


