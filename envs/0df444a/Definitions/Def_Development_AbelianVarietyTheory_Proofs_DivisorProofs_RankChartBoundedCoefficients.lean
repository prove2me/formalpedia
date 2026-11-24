-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficients
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficients
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:31:57.034258+00:00
-- url     : https://prove2.me/theorems/593b0660-73a0-4926-b2d1-acb233a8cb86
-- title:
--   Rank Chart Bounded Coefficients
-- statement:
--   Definitions and structural lemmas for Rank Chart Bounded Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartBoundedCoefficients.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IndicatorBoxEqCharSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
namespace GlobalTheory.RankChart
open ValuativeRel
def coeffOnChart {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] (τ : R → D)
    (Y : Matrix (R ⊕ T) D k) : Matrix T R k :=
  (Y.submatrix Sum.inl τ).det⁻¹ • (Y.toRows₂.submatrix id τ * (Y.submatrix Sum.inl τ).adjugate)
end GlobalTheory.RankChart
end


