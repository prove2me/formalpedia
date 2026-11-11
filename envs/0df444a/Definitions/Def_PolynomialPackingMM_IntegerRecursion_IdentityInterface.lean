-- Prove2me | Definitions.Def_PolynomialPackingMM_IntegerRecursion_IdentityInterface
-- name    : PolynomialPackingMM_IntegerRecursion_IdentityInterface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:20.894925+00:00
-- url     : https://prove2.me/theorems/1716d04f-8190-4fc7-94b8-08a6822d0807
-- title:
--   Rational identity arrays as bilinear data and ordered integer block substitution
-- statement:
--   A finite coefficient array is interpreted as rank-$r$ rational bilinear data for ordinary $v\times v$ matrix multiplication. The associated integer block output is
--
--   $$\sum_{\nu=1}^r \widetilde w_{o\nu}\left(\sum_a\widetilde\ell_{\nu a}A_a\right)\left(\sum_b\widetilde m_{\nu b}B_b\right),$$
--
--   where tildes denote the denominator-cleared integer coefficients and the blocks are arbitrary integer square matrices. Each $A$ block precedes its $B$ block; no block commutativity is imposed.
--
--   This interface connects scalar coefficient matching with the source's noncommuting block substitution. It defines the expressions only; the denominator-clearing and block-correctness equalities remain theorem obligations.
-- source:
--   Rafael Pass, STOC 2027 submission #1507 (October 2026), printed p. 19 (PDF 20), §4.3, proof of Theorem 1.1, ordered block substitution and denominator clearing; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1507.pdf; SHA256 8b32ede93c8ade8e982503a0a1eec78b50621e6fcf86eba92bef2e77847b26ba

import Definitions.Def_PolynomialPackingMM_IntegerRecursion_RecursiveCompiler
import Definitions.Def_PolynomialPackingMM_IntegerRecursion_Packing

namespace PolynomialPackingMM.IntegerRecursion

open scoped BigOperators

/-- Interpret the finite coefficient arrays as the paper's rank-r rational bilinear data. -/
noncomputable def IdentityData.asBilinear (D : IdentityData) (hv : 0 < D.v) :
    BilinearData [matrixProduct ⟨D.v, hv⟩] D.r where
  left ν a := rationalLaurent (D.leftCoeff ν (a.2.val.2.1 * D.v + a.2.val.2.2))
  right ν b := rationalLaurent (D.rightCoeff ν (b.2.val.2.1 * D.v + b.2.val.2.2))
  weight o ν := rationalLaurent (D.outputCoeff (o.2.val.2.1 * D.v + o.2.val.2.2) ν)

/-- Ordered substitution of arbitrary square integer matrix blocks. -/
def IdentityData.blockOutput (D : IdentityData) (s : ℕ)
    (A B : ℕ → Matrix (Fin s) (Fin s) ℤ) (o : ℕ) : Matrix (Fin s) (Fin s) ℤ :=
  ∑ ν : Fin D.r, D.clearCoefficient (D.outputCoeff o ν) •
    ((∑ a : Fin (D.v ^ 2), D.clearCoefficient (D.leftCoeff ν a) • A a) *
      (∑ b : Fin (D.v ^ 2), D.clearCoefficient (D.rightCoeff ν b) • B b))

end PolynomialPackingMM.IntegerRecursion


