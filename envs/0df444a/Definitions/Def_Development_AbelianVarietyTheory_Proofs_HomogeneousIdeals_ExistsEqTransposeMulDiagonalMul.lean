-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:45.031457+00:00
-- url     : https://prove2.me/theorems/a6039f1e-f85b-43ca-b904-b10f4c698e43
-- title:
--   Exists Eq Transpose Mul Diagonal Mul
-- statement:
--   Definitions and structural lemmas for Exists Eq Transpose Mul Diagonal Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsEqTransposeMulDiagonalMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
namespace GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def siegelGaussIntegral {ι : Type*} [Fintype ι] (σ : Matrix ι ι ℂ) : ℂ :=
  ∫ x : ι → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))))
end GlobalTheory


