-- Prove2me | Definitions.Def_LawLocalComp_clauseL3
-- name    : LawLocalComp_clauseL3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:25.116873+00:00
-- url     : https://prove2.me/theorems/4c620efd-dd43-4e10-b401-34cfb8523a3a
-- title:
--   Theorem 1.1, row 3 lower: actual conditional means, both resources, $\varepsilon\le2^{-40}$
-- statement:
--   There is an absolute $c>0$ such that for all $N,q$ with $\min\{N,q\}\ge2$, every rational $0<\varepsilon\le2^{-40}$ and every map $\Phi$ that is a conditional-mean replacement on every rational law and satisfies the maximum-norm comparison (14) on all selections admitted by both resources, some rational input has at least $c\,J(\varepsilon,N,q)$ positive output atoms.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; Theorem 6.2, p.10, and its proof (CM column), pp.10–12

import Mathlib
import Definitions.Def_LawLocalComp_RobustContract
import Definitions.Def_LawLocalComp_IsCondMean
import Definitions.Def_LawLocalComp_Jfun

namespace LawLocalComp

/-- **Row 3 lower of Theorem 1.1 (actual conditional means, both resources, `ε ≤ 2^{-40}`).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

Every law-local actual conditional-mean map satisfying (14) for the maximum norm under both
resources has at least `c J(ε, N, q)` positive output atoms on some rational input (Theorem 6.2,
p.10: "The lower uses only maximum norms and permits unordered/randomly split labels").
-/
def clauseL3 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N q : ℕ, 2 ≤ min N q → ∀ ε : ℚ, 0 < ε → ε ≤ 1 / 2 ^ 40 →
    ∀ Φ : Law → Law, (∀ X : Law, IsRatLaw X → IsCondMean X (Φ X)) →
      RobustContract Φ (.both N q) (fun _ => True) (1 + ε) →
      ∃ X : Law, IsRatLaw X ∧ c * Jfun ε N q ≤ (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)

end LawLocalComp


