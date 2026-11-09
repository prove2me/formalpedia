-- Prove2me | Definitions.Def_SkipListConc_failuresBefore
-- name    : SkipListConc_failuresBefore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:02.525669+00:00
-- url     : https://prove2.me/theorems/7c4b671d-4eda-4a59-9e41-9e127a8b353d
-- title:
--   Failures $N_r$ before the $r$-th success
-- statement:
--   For a sequence of trials $\xi_1,\xi_2,\dots$ (success $=1$), $N_r$ is the **number of failures before the $r$-th success**. If $\xi_1,\xi_2,\dots$ are i.i.d. Bernoulli$(p)$, then $N_r\sim\mathrm{NB}(r,p)$.
--
--   **Formalization Note** Valued in $\mathbb N\cup\{\infty\}$ ($N_r=\infty$ if there are fewer than $r$ successes); trials are indexed from $0$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.1, pp.20–21

import Mathlib

namespace SkipListConc

open Classical in
/-- `N_r`, the number of failures before the `r`-th success in a sequence of trials
`B 0, B 1, …` (`true` = success) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists:
Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Lemma 4.1,
pp.20–21). If the first `n` trials are the shortest prefix with `r` successes, `N_r = n − r`.

**Formalization Note** Valued in `ℕ∞`: `N_r = ⊤` if there are fewer than `r` successes in total.
Trials are indexed from `0` (the paper's `ξ_1, ξ_2, …`). -/
noncomputable def failuresBefore {Ω : Type*} (B : ℕ → Ω → Bool) (r : ℕ) (ω : Ω) : ℕ∞ :=
  if h : ∃ n, r ≤ ((Finset.range n).filter fun i => B i ω = true).card then
    ((Nat.find h - r : ℕ) : ℕ∞)
  else ⊤

end SkipListConc


