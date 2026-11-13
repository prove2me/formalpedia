-- Prove2me | Definitions.Def_AuditAdapt_openLoopMarginal
-- name    : AuditAdapt_openLoopMarginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:00:35.964563+00:00
-- url     : https://prove2.me/theorems/f0d1bc49-2dac-4d5f-abe0-7d99a85c9319
-- title:
--   Open-loop marginal $\nu^\pi$ and average action distribution $\bar p^\pi_t$
-- statement:
--   For a Markov policy $\pi$ with state laws $d^\pi_t$, the **average action distribution** at step $t$ is
--
--   $$
--   \bar p^\pi_t(a)=\sum_{s\in\mathcal S}d^\pi_t(s)\,\pi_t(a\mid s),\qquad a\in\mathcal A,
--   $$
--
--   the action marginal $P^A_t$ of the joint law $P_t(s,a)=d^\pi_t(s)\pi_t(a\mid s)$. The **open-loop marginal** of $\pi$ is the policy $\nu^\pi$ that ignores the state:
--
--   $$
--   \nu^\pi_t(\cdot\mid s)=\bar p^\pi_t\quad\text{for all }s .
--   $$
--
--   The adaptivity cost $J(\pi)-J(\nu^\pi)$ compares $\pi$ with the state-blind policy that plays the same actions on average.
--
--   **Formalization Note** `marginal M π t` is $\bar p^\pi_{t+1}$ (0-based layers) and `openLoopMarginal M π` is a `Policy` of the published layer, a function `ℕ → S → A → ℝ`. That $\nu^\pi$ is a Markov policy whenever $\pi$ is, is a theorem of the mission.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Definition 2.1 (Open-loop marginal), p.3

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw

namespace AuditAdapt

open FoundationsRL.RLBasics

/-- The average action distribution `p̄^π_t(a) = ∑_s d^π_t(s) π_t(a | s)` of a Markov policy
`π` (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), Definition 2.1, p.3). It is also the action marginal `P^A_t` of the joint law
`P_t(s, a) = d^π_t(s) π_t(a | s)` (§2, p.3).

**Formalization Note** Layers are 0-based (`marginal M π t` is the paper's `p̄^π_{t+1}`). -/
noncomputable def marginal {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (t : ℕ) (a : A) : ℝ :=
  ∑ s : S, stateLaw M π t s * π t s a

/-- The open-loop marginal `ν^π` of a Markov policy `π` (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), Definition 2.1, p.3):
the policy with `ν^π_t(· | s) = p̄^π_t` for all `s`.

**Formalization Note** Layers are 0-based. `ν^π` is a `Policy` of the published layer (a
function `ℕ → S → A → ℝ`); that it is a Markov policy (`IsPolicy`) whenever `π` is, is a
theorem of the mission, not part of the definition. -/
noncomputable def openLoopMarginal {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) : Policy S A H :=
  fun t _ a => marginal M π t a

end AuditAdapt


