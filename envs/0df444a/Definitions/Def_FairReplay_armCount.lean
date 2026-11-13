-- Prove2me | Definitions.Def_FairReplay_armCount
-- name    : FairReplay_armCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:26.004469+00:00
-- url     : https://prove2.me/theorems/948a46bb-bc8b-451d-bbfc-a20adee44e9a
-- title:
--   Rounds spent on one replay action before stopping, $N_S$
-- statement:
--   For an action $i$, a stopping time $\tau$ and a trajectory $\omega=((A_1,X_1),(A_2,X_2),\dots)$, the **action count**
--
--   $$
--   N_i(\tau)=\#\{t\le\tau:\ A_t=i\}\in[0,\infty]
--   $$
--
--   is the number of rounds before stopping in which action $i$ was taken. It is the paper's $N_S$ in the stopped change-of-measure inequality (138).
--
--   **Formalization Note** Trajectory coordinate $t\ge 0$ is round $t+1$, so the counted coordinates are those with $t<\tau(\omega)$. This is the same expression as in the platform's Proved `BanditAlgorithm.best_arm_identification_stopping_change_of_measure`.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), App. E, eq. (138), p.34 (PDF p.36)

import Mathlib
import Definitions.Def_BanditTrajectory

open MeasureTheory

namespace FairReplay

/-- **Number of rounds spent on one replay action before stopping** `N_S` (Sah, Zhang, Lian,
*Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of
2026-11-03, sha256 e23940a0…, App. E, eq. (138), p.34 (PDF p.36): "E0,η[NS]").

`armCount i τ ω` counts the rounds `t < τ ω` of the trajectory `ω` in which action `i` was taken.

**Formalization Note** Trajectory coordinate `t` is round `t + 1`, so the rounds before stopping
are the coordinates `t` with `t < τ ω`; the count is in `ℝ≥0∞` and is `∞` when `τ ω = ⊤` and `i`
is taken infinitely often. This is the expression used in the platform's Proved
`BanditAlgorithm.best_arm_identification_stopping_change_of_measure`. -/
noncomputable def armCount {k : ℕ} (i : Fin k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ω : ℕ → Fin k × ℝ) : ENNReal :=
  ∑' t : ℕ, if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then 1 else 0

end FairReplay


