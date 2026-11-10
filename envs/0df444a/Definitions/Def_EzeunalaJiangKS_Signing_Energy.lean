-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_Energy
-- name    : EzeunalaJiangKS_Signing_Energy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:06:16.505555+00:00
-- url     : https://prove2.me/theorems/16ab7b2e-4cd0-4a55-9719-94d6977ae0a5
-- title:
--   Fixed-t variations and barrier energy
-- statement:
--   For a direction $h$ supported on active coordinates, apply the inverse of $L$ to $(\sum_i\alpha_i h_iA_i,-\sum_i\beta_i h_iA_i)$ to obtain $(\dot X,\dot Y)$. Set
--   $$E_h=\operatorname{ReTr}(PX^{-1}\dot XX^{-1}\dot XX^{-1})+\operatorname{ReTr}(QY^{-1}\dot YY^{-1}\dot YY^{-1}).$$
--   This is the energy of the fixed-$t$ feasible path, not the derivative of the optimizing triple with changing $t$. It is determined by the chosen optimizer, multipliers, and actual linearized inverse. No freely chosen quadratic form or energy estimate is supplied.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §4.2, (18)–(20), printed p. 13 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_ScalarData

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

def variation {N d : ℕ} (A : Fin N → CMat d) (x₀ x h : State N) : PairMat d :=
  let z := optimizer A x₀ x
  linearizedInverse A x z.2.1 z.2.2
    ((∑ i ∈ active x, (alpha A x₀ x i * h i) • A i),
     -∑ i ∈ active x, (beta A x₀ x i * h i) • A i)

def energy {N d : ℕ} (A : Fin N → CMat d) (x₀ x h : State N) : ℝ :=
  let z := optimizer A x₀ x
  let X := z.2.1
  let Y := z.2.2
  let pq := dual A x₀ x
  let V := variation A x₀ x h
  tr (pq.1 * X⁻¹ * V.1 * X⁻¹ * V.1 * X⁻¹) +
    tr (pq.2 * Y⁻¹ * V.2 * Y⁻¹ * V.2 * Y⁻¹)

end EzeunalaJiangKS.Signing


