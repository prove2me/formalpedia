-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapReflection
-- name    : ZetaNine_CoefficientMapReflection
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T18:51:57.841489+00:00
-- url     : https://prove2.me/theorems/46306e7b-9adc-43aa-925d-1e9ee80c56a6
-- title:
--   Actual reflection variable, local coefficient totals and strong proper domain
-- statement:
--   For $n\ge0$ and $W\in\mathbb Q[X]$, let $c^W_{n,j,s}$ be the actual local coefficient of the genuine shifted numerator/unit denominator quotient from the Base/Jet/Injectivity/PF definition chain. Define the reflection variable $V_n(X)=-X-n$ and the finite coefficient total $\rho_{n,s}(W)=\sum_{j=0}^{n}c^W_{n,j,s}$. Define
--
--   $$\mathrm{StrongProper}(n,W)\iff 2n+2\operatorname{natdeg}W\le9(n+1)-2.$$
--
--   Finally define the genuine partial basis $B_{n,j,s}=(\prod_{0\le k\le n,\ k\ne j}(X+k))^9(X+j)^{9-s}$. These are four actual objects/conditions, not a reflection, cancellation or invertibility conclusion encoded as an assumption. StrongProper is stricter than the strict proper-degree condition.
-- source:
--   Zeta(9) actual finite reflection and coefficient-total research: missions/zeta9/research/coefficient-map-reflection-2026-10-03.md. Frozen source missions/zeta9/formalization/CoefficientMapReflection.lean, SHA256 8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707. This uses the actual finite product numerator/denominator, genuine weighted formal local coefficients and proved finite partial-fraction identity.

import Definitions.Def_ZetaNine_CoefficientMapPartialFractions


set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapReflection

open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity CoefficientMapPartialFractions

def reflectionVariable (n : ℕ) : ℚ[X] := -X - C (n : ℚ)

def rho (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n j s W

def StrongProperMultiplier (n : ℕ) (W : ℚ[X]) : Prop :=
  2 * n + 2 * W.natDegree ≤ 9 * (n + 1) - 2

def partialBasis (n j s : ℕ) : ℚ[X] :=
  clearedPolePolynomial n j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)

end ZetaNine.CoefficientMapReflection


