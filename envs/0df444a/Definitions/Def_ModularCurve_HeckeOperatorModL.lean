-- Prove2me | Definitions.Def_ModularCurve_HeckeOperatorModL
-- name    : ModularCurve_HeckeOperatorModL
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/0712feaf-48e9-5e3a-a44f-7551681a87be
-- title:
--   Hecke operator mod ℓ: Frobenius pushforward plus pullback
-- statement:
--   Fix a prime $\ell$, a field $K$ of characteristic $\ell$ and a level $N$, and let $\bar F_N = \mathrm{modularFunctionFieldFullC}\ K\ N$ be the intermediate field of $K$-Laurent series generated over $K$ by the reductions $\mathrm{qExpand}\ K\ d\,(\bar j)$ of the $j$-expansion in $q^{d}$, for the nonzero divisors $d \mid N$; let $\mathrm{JZeroC}\ K\ N = \mathrm{Pic}^0(K,\bar F_N)$ be the associated degree-zero divisor class group. The Frobenius endomorphism $\mathrm{frobeniusModL}$ of $\bar F_N$ is the $K$-algebra map $q \mapsto q^{\ell}$ on expansions; it is integral, and along it one has the divisor pushforward and pullback maps. Two operators are defined. First, under the hypothesis `HasPrincipalDivisors` for $\bar F_N/K$, `heckeDivOperatorModL` is the additive endomorphism $\mathrm{Fr}_{*} + \mathrm{Fr}^{*}$ of the divisor group $\mathrm{Divisor}\ K\ \bar F_N$. Second, `heckeOperatorModL` is the additive endomorphism $\mathrm{Fr}_{*} + \mathrm{Fr}^{*}$ of $\mathrm{JZeroC}\ K\ N$, formed from the two total maps `frobeniusPushforwardModL` and `frobeniusPullbackModL`, each of which is defined by the case distinction on `FrobeniusInputsModL K N ℓ` (the existence of a `HasPrincipalDivisors` structure, of module-finiteness of $\bar F_N$ over itself along Frobenius, of the fundamental identity $\sum_{w \mid v} e_w \deg w = [\bar F_N : \bar F_N]_{\mathrm{Fr}} \deg v$, and of the norm formula for pushforward of principal divisors) and is zero when those inputs fail. Accordingly `heckeOperatorModL_of_not` records that the operator vanishes when `FrobeniusInputsModL` does not hold, while `heckeOperatorModL_mk`, given all four inputs, computes the operator on the class of a degree-zero divisor $D$ as the class of $\mathrm{Fr}_{*}D + \mathrm{Fr}^{*}D$; `coe_frobeniusDegZero_add` identifies the underlying divisor of that sum with `heckeDivOperatorModL` applied to $D$. The remaining declarations are the defining unfoldings of the two operators.
--
--   **Relation to Mathlib.** Mathlib has no modular curves, Jacobians of function fields or Hecke operators; places, divisors, the pushforward and pullback along an integral algebra map, `Pic0`, and the Frobenius endomorphism of the reduced modular function field are all the project's own constructions, on which these definitions are built.
--
--   **Where it is used.** This is the mod $\ell$ Hecke operator in the form in which the Eichler–Shimura congruence relation expresses it, namely as the sum of the two Frobenius correspondences on the special fibre; the operator on the Jacobian is here taken as that sum by definition. The comparison with the characteristic-zero Hecke operator on $J_0(N)$ under reduction is a separate statement, and feeds the congruence relation into the study of the mod $\ell$ Galois representations attached to modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_HeckeOperatorModL.lean

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Divisors

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
variable [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]

def heckeDivOperatorModL :
    Divisor K (modularFunctionFieldFullC K N) →+ Divisor K (modularFunctionFieldFullC K N) :=
  frobeniusDivPushforwardModL K N ℓ + frobeniusDivPullbackModL K N ℓ

theorem heckeDivOperatorModL_apply (D : Divisor K (modularFunctionFieldFullC K N)) :
    heckeDivOperatorModL K N ℓ D =
      frobeniusDivPushforwardModL K N ℓ D + frobeniusDivPullbackModL K N ℓ D :=
  rfl

end Divisors

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def heckeOperatorModL : JZeroC K N →+ JZeroC K N :=
  frobeniusPushforwardModL K N ℓ + frobeniusPullbackModL K N ℓ

theorem heckeOperatorModL_apply (x : JZeroC K N) :
    heckeOperatorModL K N ℓ x = frobeniusPushforwardModL K N ℓ x + frobeniusPullbackModL K N ℓ x :=
  rfl

variable {K N ℓ}

theorem heckeOperatorModL_mk [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin)
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    heckeOperatorModL K N ℓ (Pic0.mk D) =
      Pic0.mk (frobeniusDegZeroPushforwardModL K N ℓ D + frobeniusDegZeroPullbackModL K N ℓ hFI D) := by
  rw [heckeOperatorModL_apply, frobeniusPushforwardModL_mk hfin hFI hN,
    frobeniusPullbackModL_mk hfin hFI hN, Pic0.mk_add]

theorem coe_frobeniusDegZero_add [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    ((frobeniusDegZeroPushforwardModL K N ℓ D + frobeniusDegZeroPullbackModL K N ℓ hFI D :
        Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
        Divisor K (modularFunctionFieldFullC K N)) =
      heckeDivOperatorModL K N ℓ (D : Divisor K (modularFunctionFieldFullC K N)) :=
  rfl

theorem heckeOperatorModL_of_not (h : ¬ FrobeniusInputsModL K N ℓ) : heckeOperatorModL K N ℓ = 0 := by
  rw [heckeOperatorModL, frobeniusPushforwardModL_of_not h, frobeniusPullbackModL_of_not h]
  exact add_zero (0 : JZeroC K N →+ JZeroC K N)

end Jacobian

end ModularCurve

end


