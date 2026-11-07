-- Prove2me | Definitions.Def_SmoothedNash_maxAct
-- name    : SmoothedNash_maxAct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:57.17708+00:00
-- url     : https://prove2.me/theorems/61a39005-8a69-4fad-b280-e612b0574040
-- title:
--   The last coordinate $\max A_i$
-- statement:
--   For a support profile $A$ and a player $i$, $\max A_i$ is the largest action in $A_i$. In the grids of Lemma 2.1 and their children, the coordinate $\max A_i$ is the one set last, so that player $i$'s coordinates sum to $1$.
--
--   **Formalization Note** The maximum is taken in the order of `Fin n`.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile

namespace SmoothedNash

/-- The coordinate `max A_i` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14): the largest action of `A_i`, which absorbs
the rounding slack of player `i` in the grids and their children.

**Formalization Note** The maximum is taken in the order of `Fin n`. -/
def maxAct {m n : ℕ} (A : SupportProfile m n) (i : Fin m) : Fin n :=
  (A.1 i).max' (A.2 i)

end SmoothedNash


