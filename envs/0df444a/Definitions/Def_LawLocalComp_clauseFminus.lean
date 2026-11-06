-- Prove2me | Definitions.Def_LawLocalComp_clauseFminus
-- name    : LawLocalComp_clauseFminus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:40.040187+00:00
-- url     : https://prove2.me/theorems/7666080b-798c-4dd0-a527-fd09597baece
-- title:
--   Theorem 1.1: robust all-$C$ lower $\Omega_C(1+\log\log(M+2))$
-- statement:
--   For every fixed $C>1$ there is $c_2>0$ such that for every resource with $M\ge1$ and every map $\Phi$ satisfying $C^{-1}\mathbb E\|L\|_\infty\le\mathbb E\|\tilde L\|_\infty\le C\,\mathbb E\|L\|_\infty$ on admitted selections of lattice-log-concave laws, some lattice-log-concave input has at least $c_2(1+\log\log(M+2))$ positive output atoms.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; proof in "Fixed-distortion lower in Theorem 1.1", p.14

import Mathlib
import Definitions.Def_LawLocalComp_RobustContract
import Definitions.Def_LawLocalComp_IsLatticeLC
import Definitions.Def_LawLocalComp_Resource_M

namespace LawLocalComp

/-- **Theorem 1.1: robust all-`C` lower `Ω_C(1 + log log(M + 2))`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

For every fixed `C > 1`, every law-local map satisfying the maximum-norm comparison with factor `C`
on lattice-log-concave laws has `Ω_C(1 + log log(M + 2))` positive output atoms on some
lattice-log-concave input.
-/
def clauseFminus : Prop :=
  ∀ C : ℝ, 1 < C → ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ R : Resource, 1 ≤ R.M → ∀ Φ : Law → Law,
    RobustContract Φ R IsLatticeLC C →
      ∃ X : Law, IsLatticeLC X ∧
        c₂ * (1 + Real.log (Real.log (R.M + 2))) ≤ (((Φ X).w.support.filter (fun y => 0 < y)).card : ℝ)

end LawLocalComp


