-- Prove2me | Definitions.Def_SmoothedNash_q
-- name    : SmoothedNash_q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:07.068099+00:00
-- url     : https://prove2.me/theorems/6307105a-6a16-4901-ab24-451db1ada1f5
-- title:
--   Grid denominators $q_t = 2^t \max\{1, \lceil R/m \rceil\}$
-- statement:
--   For a support profile $A$ with dimension $R$, the grid denominators of Lemma 2.1 are
--   $$
--   q_0 = \max\{1, \lceil R/m \rceil\}, \qquad q_t = 2^t q_0 \quad (t \ge 0).
--   $$
--   The level-$t$ grid consists of the profiles in $K_A$ whose coordinates are multiples of $1/q_t$.
--
--   **Formalization Note** $\lceil R/m \rceil$ is the natural-number ceiling division $(R + m - 1)/m$, equal to $\lceil R/m \rceil$ for $m \ge 1$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_R

namespace SmoothedNash

/-- The grid denominators `q_0 = max{1, ⌈R/m⌉}` and `q_t = 2^t q_0` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14).

**Formalization Note** `⌈R/m⌉` is the natural-number ceiling division `(R + m − 1) / m`, which
equals `⌈R/m⌉` for `m ≥ 1`. -/
def q {m n : ℕ} (A : SupportProfile m n) (t : ℕ) : ℕ :=
  2 ^ t * max 1 ((R A + m - 1) / m)

end SmoothedNash


