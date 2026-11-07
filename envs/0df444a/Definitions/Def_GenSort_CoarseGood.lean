-- Prove2me | Definitions.Def_GenSort_CoarseGood
-- name    : GenSort_CoarseGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:59.966994+00:00
-- url     : https://prove2.me/theorems/078ef72b-49d5-4fc1-8b67-b463c87d15c2
-- title:
--   Good event of Claim 3.1: $\mathrm{dist}_F(\pi,\sigma) \le f/(2^{28}\log^2 n)$
-- statement:
--   For an edge set $F$ with $f = |F|$, the coarse prediction $\sigma$ is **good** if
--   $$
--   \mathrm{dist}_F(\pi, \sigma) \le \frac{f}{2^{28} \log^2 n}.
--   $$
--   This is the good event of Claim 3.1, assumed in Claims 3.4 and 3.10.
--
--   **Formalization Note** $\log = \log_2$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_GenSort_distOrd

namespace GenSort

/-- **The good event of Claim 3.1**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.1, p.5 (PDF p.7), and its use in Claims 3.4 and
3.10: `dist_F(π, σ) ≤ f / (2^28 log² n)` with `f = |F|`.

**Formalization Note.** `log` is `log₂`. -/
def CoarseGood {n : ℕ} (F : Finset (Sym2 (Fin n))) (π σ : Equiv.Perm (Fin n)) : Prop :=
  (distOrd F π σ : ℝ) ≤ F.card / (2 ^ 28 * Real.logb 2 n ^ 2)

end GenSort


