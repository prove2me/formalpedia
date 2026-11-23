-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:05.955813+00:00
-- url     : https://prove2.me/theorems/732d2b95-4c5f-4006-8699-5e3b2677b1e8
-- title:
--   Dual Lattice Image Eq Lattice Image Trace Dual
-- statement:
--   Definitions and structural lemmas for Dual Lattice Image Eq Lattice Image Trace Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualLatticeImageEqLatticeImageTraceDual.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
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
namespace GlobalTheory.LipschitzTR
section
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
end
end GlobalTheory.LipschitzTR


