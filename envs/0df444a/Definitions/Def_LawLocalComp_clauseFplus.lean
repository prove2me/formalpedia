-- Prove2me | Definitions.Def_LawLocalComp_clauseFplus
-- name    : LawLocalComp_clauseFplus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:14:06.053569+00:00
-- url     : https://prove2.me/theorems/7bcfc015-e8ba-4b7b-88c0-72d79aa5b4f7
-- title:
--   Theorem 1.1: fixed-distortion upper $O_C(1+\log\log(M+2))$
-- statement:
--   For every fixed $C>1$ there are $c_1>0$ and maps $\Phi_R$, computable in time polynomial in the input bits and the bit lengths of the resources on lattice-log-concave inputs, such that for every resource with $M\ge1$ the output on lattice-log-concave laws is a rational conditional-mean replacement preserving mean and point masses with at most $c_1(1+\log\log(M+2))$ atoms, and $\mathbb E g(\tilde L)\le\mathbb E g(L)\le C\,\mathbb E g(\tilde L)$ for every admitted selection of lattice-log-concave laws.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; Proposition 7.3, p.13

import Mathlib
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_Contract
import Definitions.Def_LawLocalComp_PolyLawMap
import Definitions.Def_LawLocalComp_IsLatticeLC
import Definitions.Def_LawLocalComp_Resource_M
import Definitions.Def_LawLocalComp_Resource_params

namespace LawLocalComp

/-- **Theorem 1.1: fixed-distortion upper `O_C(1 + log log(M + 2))`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

For every fixed distortion `C > 1`, a polynomial-time map on lattice-log-concave laws with
`O_C(1 + log log(M + 2))` atoms satisfying `E g(L̃) ≤ E g(L) ≤ C E g(L̃)`.
-/
def clauseFplus : Prop :=
  ∀ C : ℝ, 1 < C → ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ Φ : Resource → Law → Law,
    PolyLawMap Resource.params (fun _ => 0) IsLatticeLC Φ ∧
    ∀ R : Resource, 1 ≤ R.M →
      (∀ X : Law, IsLatticeLC X → IsGoodOutput X (Φ R X) ∧
        ((Φ R X).w.support.card : ℝ) ≤ c₁ * (1 + Real.log (Real.log (R.M + 2)))) ∧
      Contract (Φ R) R IsLatticeLC C

end LawLocalComp


