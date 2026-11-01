-- Prove2me | Definitions.Def_OfflineToOnline_fullHistoryPlay
-- name    : OfflineToOnline_fullHistoryPlay
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:17.163813+00:00
-- url     : https://prove2.me/theorems/4ba6f767-98cd-46ff-a5a1-dc12eb21e817
-- title:
--   Full-history player 1 strategy and its play
-- statement:
--   A **full-history strategy** for player 1 chooses its action at round $t$ from the past action pairs $(x_1,y_1),\dots,(x_{t-1},y_{t-1})$. Its **play** against a sequence $y_1,y_2,\dots$ of player 2 actions is defined by this recursion.
--
--   These are the player 1 strategies of Definition 3; they appear in the "only if" direction of Theorem 1 and in the notion of approachability of Proposition 1.
--
--   **Formalization Note** Rounds are $0$-indexed and strategies are deterministic.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 3, p.12

import Mathlib

namespace OfflineToOnline

/-- A deterministic full-history player 1 strategy (Definition 3, p.12): at round `t` it maps
the past action pairs `(x_s, y_s)_{s < t}` to an action. -/
abbrev FullHistoryStrategy (m k : ℕ) : Type :=
  (t : ℕ) → (Fin t → (Fin m → ℝ) × (Fin k → ℝ)) → (Fin m → ℝ)

/-- The play of a full-history strategy `B` against a sequence `y` of player 2 actions:
`x_t = B_t((x_s, y_s)_{s < t})`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 3, p.12.

Formalization Note: rounds are `0`-indexed. -/
noncomputable def fullHistoryPlay {m k : ℕ} (B : FullHistoryStrategy m k)
    (y : ℕ → Fin k → ℝ) : ℕ → Fin m → ℝ
  | t => B t (fun s => (fullHistoryPlay B y s.1, y s.1))
termination_by t => t
decreasing_by exact s.2

end OfflineToOnline


