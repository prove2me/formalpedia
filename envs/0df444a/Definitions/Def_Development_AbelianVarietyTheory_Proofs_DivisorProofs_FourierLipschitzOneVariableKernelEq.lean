-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:41.15999+00:00
-- url     : https://prove2.me/theorems/b131b0ea-ec35-4708-91c5-fe4093b87caa
-- title:
--   Fourier Lipschitz One Variable Kernel Eq
-- statement:
--   Definitions and structural lemmas for Fourier Lipschitz One Variable Kernel Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierLipschitzOneVariableKernelEq.lean

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
namespace GlobalTheory.LipschitzTR
open Set Filter Topology
end GlobalTheory.LipschitzTR


