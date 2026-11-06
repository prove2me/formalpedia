-- Prove2me | Definitions.Def_LawLocalComp_clauseL2
-- name    : LawLocalComp_clauseL2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:34.663071+00:00
-- url     : https://prove2.me/theorems/e675281d-4ed1-4a13-9472-9426ad65b825
-- title:
--   Theorem 1.1, row 2 lower: robust, rank only, $\varepsilon\le1/1024$
-- statement:
--   There is an absolute $c>0$ such that for every $q\ge2$, every rational $0<\varepsilon\le1/1024$ and every map $\Phi$ satisfying (14) on all selections of rank at most $q$, some rational input has at least $c\,\varepsilon^{-1}\log(q+1)$ positive output atoms.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; proof in "Rank lower in Theorem 1.1", p.9, (19)–(21)

import Mathlib
import Definitions.Def_LawLocalComp_RobustContract

namespace LawLocalComp

/-- **Row 2 lower of Theorem 1.1 (robust, rank only, `ε ≤ 1/1024`).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.
-/
def clauseL2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, 2 ≤ q → ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 1024 →
    ∀ Φ : Law → Law, RobustContract Φ (.rank q) (fun _ => True) (1 + ε) →
      ∃ X : Law, IsRatLaw X ∧
        c * (1 / (ε : ℝ)) * Real.log (q + 1) ≤ (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)

end LawLocalComp


