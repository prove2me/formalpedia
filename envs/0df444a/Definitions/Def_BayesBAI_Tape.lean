-- Prove2me | Definitions.Def_BayesBAI_Tape
-- name    : BayesBAI_Tape
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:52.426978+00:00
-- url     : https://prove2.me/theorems/07de9c61-046d-4bb8-bef5-cec310270570
-- title:
--   The reward tape of a $K$-armed Bernoulli bandit
-- statement:
--   A **reward tape** with $K$ arms and horizon $T$ is a table $\omega=(\omega_{i,t})_{i\in[K],\,t\in[T]}$ of bits, where $\omega_{i,t}\in\{0,1\}$ is the reward of the $t$-th pull of arm $i$.
--
--   Two-stage exploration fixes its pulls in each stage once the candidate set is known, and the first $n$ pulls of an arm read the first $n$ entries of its row, so a whole run of the algorithm is a function of the tape.
--
--   **Formalization Note.** Arms are `Fin K` and pulls are `Fin T` (0-based); `true` stands for reward $1$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §1, p.1, and §D.3, p.20

import Mathlib

namespace BayesBAI

/-- The reward tape of the Bernoulli bandit, for Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, §1,
p.1, and p.20 (`μ̂_{i,n}` is "the empirical mean of arm `i` with the first `n` samples").
Entry `(i, t)` is the reward of the `(t + 1)`-st pull of arm `i`.

**Formalization Note.** Arms are `Fin K`, and rounds of an arm are `Fin T`. Algorithm 1 fixes its pulls
in each stage once the candidate set is known, and the first `n` pulls of an arm are the first `n` tape
entries, so a tape carries the whole run. -/
abbrev Tape (K T : ℕ) : Type := Fin K → Fin T → Bool

end BayesBAI


