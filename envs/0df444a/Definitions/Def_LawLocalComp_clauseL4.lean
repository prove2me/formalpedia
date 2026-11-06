-- Prove2me | Definitions.Def_LawLocalComp_clauseL4
-- name    : LawLocalComp_clauseL4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:38.594755+00:00
-- url     : https://prove2.me/theorems/c927b5c4-1a00-4e4f-adeb-9caecfed10e3
-- title:
--   Theorem 1.1, row 4 lower: robust, lattice-LC, $\varepsilon\le2^{-20}$
-- statement:
--   There is an absolute $c>0$ such that for every resource $R$ with $M\ge2$, every rational $0<\varepsilon\le2^{-20}$ and every map $\Phi$ satisfying (14) on all admitted selections of lattice-log-concave laws, some lattice-log-concave input has at least $c\,A(\varepsilon,M)$ positive output atoms.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; proof in "LC accuracy lower in Theorem 1.1", pp.15–16, (39)–(43)

import Mathlib
import Definitions.Def_LawLocalComp_RobustContract
import Definitions.Def_LawLocalComp_IsLatticeLC
import Definitions.Def_LawLocalComp_Afun
import Definitions.Def_LawLocalComp_Resource_M

namespace LawLocalComp

/-- **Row 4 lower of Theorem 1.1 (robust, lattice-LC, `ε ≤ 2^{-20}`).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

Every law-local map satisfying (14) on selections of lattice-log-concave laws admitted by `R` has at
least `c A(ε, M)` positive output atoms on some lattice-log-concave input.
-/
def clauseL4 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ R : Resource, 2 ≤ R.M → ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 ^ 20 →
    ∀ Φ : Law → Law, RobustContract Φ R IsLatticeLC (1 + ε) →
      ∃ X : Law, IsLatticeLC X ∧ c * Afun ε R.M ≤ (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)

end LawLocalComp


