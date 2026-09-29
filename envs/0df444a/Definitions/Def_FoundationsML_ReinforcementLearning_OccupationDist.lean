-- Prove2me | Definitions.Def_FoundationsML_ReinforcementLearning_OccupationDist
-- name    : FoundationsML_ReinforcementLearning_OccupationDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:33:15.215631+00:00
-- url     : https://prove2.me/theorems/879d4b3c-0871-46fb-b423-1ef94f8bb17e
-- title:
--   State-occupation distribution of the policy-induced Markov chain
-- statement:
--   **Scaffolding for Definition 17.3, §17.3.2, p. 381-382, PDF p. 398-399.** For a fixed policy
--   $\pi$ started at state $s_0$, this is the distribution of the state $s_t$ reached at time
--   $t$ under the Markov chain induced by $\pi$: the point mass at $s_0$ when $t=0$, and
--   propagated one step at a time via the induced transition matrix. Not itself a book-numbered
--   definition; it is the process underlying Definition 17.3's expectation
--   $V_\pi(s)=\mathbb E_{a_t\sim\pi(s_t)}\big[\sum_t\gamma^t r(s_t,a_t)\mid s_0=s\big]$.
--
--   **Formalization Note.** `OccupationDist π P s0 0` is the point mass at `s0`;
--   `OccupationDist π P s0 (t+1)` propagates one step via `InducedTransition`, matching the
--   Markov chain's own one-step update under the mixed action distribution `π(s)` at every
--   visited state `s`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, §17.3.2, p. 381-382 (PDF p. 398-399)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition

namespace FoundationsML.ReinforcementLearning

/-- The state-occupation distribution at time `t` of the Markov chain induced by policy `π`
starting at `s0`, i.e. the distribution of `s_t` given `s_0 = s0` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, §17.3.2, p. 381-382,
PDF p. 398-399, the process underlying the expectation in Definition 17.3's `V_π(s) =
E_{a_t∼π(s_t)}[∑_t γ^t r(s_t,a_t) | s_0=s]`). Not itself a book-numbered definition; the
scaffolding needed to state `PolicyValue` as a genuine infinite-horizon expectation rather than
assuming the Bellman fixed-point equation as its definition.

**Formalization Note.** `OccupationDist π P s0 0` is the point mass at `s0`; `OccupationDist π P
s0 (t+1)` propagates one step via `InducedTransition`, matching the Markov chain's own one-step
update under the mixed action distribution `π(s)` at every visited state `s`. -/
noncomputable def OccupationDist {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (P : S → A → S → ℝ) (s0 : S) : ℕ → S → ℝ
  | 0 => fun s => if s = s0 then 1 else 0
  | (t + 1) => fun s' => ∑ s : S, OccupationDist π P s0 t s * InducedTransition π P s s'

end FoundationsML.ReinforcementLearning


