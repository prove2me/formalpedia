-- Prove2me | Definitions.Def_MasulloRH_RationalFiniteRadial
-- name    : MasulloRH_RationalFiniteRadial
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T01:37:06.498004+00:00
-- url     : https://prove2.me/theorems/da4c77a4-e280-48c1-8db2-519911ab48b5
-- title:
--   Integral finite adèles, their dilates, and rational radial test functions
-- statement:
--   In the finite adèle ring $A=\mathbb A_{\mathbb Q,f}$ let $O=\widehat{\mathbb Z}$ be the integral finite adèles and let $K=\widehat{\mathbb Z}^{\times}$ be the compact group of finite unit idèles. The diagonal embeds $\mathbb Q$ into $A$. For $k,d\in\mathbb Q$ define the sets $dO$ and $k+dO$ by multiplication and translation in $A$. The radial test space is the complex linear span of the indicator functions $\mathbf1_{dO}$ for positive rational $d$. These definitions use the actual finite adèle ring, local valuation rings, and unit subgroup.
-- source:
--   A. M. Masullo, The Music of the Primes, Example 2.1.3.1, pp. 67–68, §2.2.3, and (A.2.2.1)–(A.2.2.3). A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, §III and Appendix I, https://arxiv.org/abs/math/9811068.

import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_NumberField_AdelicBox

open IsDedekindDomain NumberField

namespace MasulloRH.RationalFinite
noncomputable section

abbrev A := FiniteAdeleRing (𝓞 ℚ) ℚ
abbrev K := FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ
abbrev O : Set A := NumberField.AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ
abbrev diag : ℚ →+* A := algebraMap ℚ A

/-- The finite-adelic dilation of the integral finite adèles by a rational number. -/
def centeredBall (d : ℚ) : Set A := (fun z : A => diag d * z) '' O

/-- A rational translate of a dilated integral subgroup. -/
def translatedBall (k d : ℚ) : Set A := (fun z : A => diag k + diag d * z) '' O

/-- The complex linear span of indicators of the positive rational dilates of the integral adèles. -/
def radialSpan : Submodule ℂ (A → ℂ) :=
  Submodule.span ℂ {f : A → ℂ | ∃ d : ℚ, 0 < d ∧ f = (centeredBall d).indicator 1}

end
end MasulloRH.RationalFinite


