-- Prove2me | Definitions.Def_LawLocalComp_clauseL1
-- name    : LawLocalComp_clauseL1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:41.389298+00:00
-- url     : https://prove2.me/theorems/bd44c69f-cebd-4d20-b080-aeebf163f099
-- title:
--   Theorem 1.1, row 1 lower: robust, horizon, $\varepsilon\le1/16384$
-- statement:
--   There is an absolute $c>0$ such that for every $N\ge2$, every rational $0<\varepsilon\le1/16384$ and every map $\Phi$ from laws to laws satisfying the robust comparison (14) on all selections of at most $N$ rational jobs, some rational input $X$ has
--   $$|\operatorname{supp}\Phi(X)\setminus\{0\}|\ \ge\ c\,\varepsilon^{-1/2}\log(N+1).$$
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; proof in "Lower bound in Theorem 1.1", §5.1, p.8, (17)

import Mathlib
import Definitions.Def_LawLocalComp_RobustContract

namespace LawLocalComp

/-- **Row 1 lower of Theorem 1.1 (robust, horizon, `ε ≤ 1/16384`).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

Every law-local map satisfying only the robust maximum-norm comparison (14) for selections of at
most `N` jobs has, on some rational input, at least `c ε^{-1/2} log(N + 1)` positive output atoms.
-/
def clauseL1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N → ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 16384 →
    ∀ Φ : Law → Law, RobustContract Φ (.horizon N) (fun _ => True) (1 + ε) →
      ∃ X : Law, IsRatLaw X ∧
        c * (1 / Real.sqrt ε) * Real.log (N + 1) ≤ (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)

end LawLocalComp


