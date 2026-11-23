-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:31.878052+00:00
-- url     : https://prove2.me/theorems/34096780-ccfd-41a2-881b-1901ad76a0b3
-- title:
--   Summable Lipschitz Lattice Norm Pow Summand
-- statement:
--   Definitions and structural lemmas for Summable Lipschitz Lattice Norm Pow Summand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableLipschitzLatticeNormPowSummand.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
namespace GlobalTheory.LipschitzTR.LhsSum
variable {F : Type} [Field F] [NumberField F]
def wt (m : ℤ) : ℝ := ((1 + |(m : ℝ)|) ^ 2)⁻¹
end GlobalTheory.LipschitzTR.LhsSum


