-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapFiniteSum
-- name    : ZetaNine_CoefficientMapFiniteSum
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T19:44:39.955167+00:00
-- url     : https://prove2.me/theorems/be5ae0fc-5c67-4931-bce7-c840f5151c7b
-- title:
--   Actual finite weighted rational sum, coefficient totals and harmonic tail
-- statement:
--   For $n,T\ge0$ and $W\in\mathbb Q[X]$, use the actual coefficients $c^W_{n,j,s}$ of the genuine local series and the existing finite harmonic number $H_N^{(s)}=\sum_{k=1}^N k^{-s}$, also for $s=0$. Define
--
--   $$\rho_{n,s}(W)=\sum_{j=0}^n c^W_{n,j,s},\qquad B_n(W)=-\sum_{j=0}^n\sum_{s=1}^9 c^W_{n,j,s}H_j^{(s)}.$$
--
--   Define the actual finite rational sum $L_{n,T}(W)=\sum_{t=1}^T R_{n,W}(t)$ and the finite shifted tail
--
--   $$E_{n,T}(W)=\sum_{j=0}^n\sum_{s=1}^9c^W_{n,j,s}(H_{T+j}^{(s)}-H_T^{(s)}).$$
--
--   These are four genuine finite definitions. No coefficient cancellation, infinite sum, reflection or convergence is encoded as a premise. The existing harmonicPower definition is unchanged.
-- source:
--   Zeta(9) actual finite harmonic summation: missions/zeta9/research/coefficient-map-finite-sum-2026-10-03.md. Frozen missions/zeta9/formalization/CoefficientMapFiniteSum.lean SHA256 b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97. Coefficients are the actual weighted formal local jets of the p=9,q=1,m=n rational function, using the genuine finite global partial-fraction identity.

import Definitions.Def_ZetaNine_CoefficientMapPartialFractions
import Definitions.Def_ZetaNine_HarmonicStability
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFiniteSum

open scoped BigOperators
open Finset Polynomial
open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions

def rho (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n j s W

def constantTerm (n : ℕ) (W : ℚ[X]) : ℚ :=
  -(∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W * harmonicPower s j)

def finiteL (n T : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ t ∈ Icc 1 T, CoefficientMap.weightedR n W (t : ℚ)

def shiftedTail (n T : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W *
      (harmonicPower s (T + j) - harmonicPower s T)

end ZetaNine.CoefficientMapFiniteSum


