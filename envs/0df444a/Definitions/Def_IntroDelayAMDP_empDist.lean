-- Prove2me | Definitions.Def_IntroDelayAMDP_empDist
-- name    : IntroDelayAMDP_empDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:57.638308+00:00
-- url     : https://prove2.me/theorems/09d9670b-63ef-4e43-9cac-0a4aeeb7aa18
-- title:
--   Empirical next-state distribution
-- statement:
--   For the list of next states observed after the visits to a pair, in order of observation, $\hat P_n(s')$ is the fraction of the first $n$ entries equal to $s'$.
--
--   **Formalization Note** It is read only for $1\le n\le N_k(s,a)$. At $n=0$ the division by zero returns the Lean default $0$, a value Eq. (16) never reads.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Section 3, p.14

import Mathlib

namespace IntroDelayAMDP

/-- **Empirical next-state distribution** `P̂_n(· | s, a)` (Section 3, p.14). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.14:
"let `P̂_n(· | s, a)` be the empirical distribution of the first `n` next states observed after
visiting `(s, a)`".

For the list `obs` of the next states observed after the visits to a pair, in order of
observation, `empDist obs n s'` is the fraction of the first `n` entries equal to `s'`.

**Formalization Note.** It is used only for `1 ≤ n ≤ length obs` (Eq. (16)); at `n = 0` the
division by `0` returns the Lean default `0`, a value Eq. (16) never reads. -/
noncomputable def empDist {St : Type} [DecidableEq St] (obs : List St) (n : ℕ) (s' : St) : ℝ :=
  ((obs.take n).count s' : ℝ) / n

end IntroDelayAMDP


