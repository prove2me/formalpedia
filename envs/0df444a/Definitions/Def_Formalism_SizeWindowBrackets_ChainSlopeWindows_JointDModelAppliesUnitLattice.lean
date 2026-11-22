-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:39.895533+00:00
-- url     : https://prove2.me/theorems/7d4e74c4-bcd5-4f51-b187-f9946f4aae71
-- title:
--   Joint DModel Applies Unit Lattice
-- statement:
--   Definitions and structural lemmas for Joint DModel Applies Unit Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
section Lin
variable {m n o : Type} [Fintype m] [Fintype n] [Fintype o] [DecidableEq m] [DecidableEq n]
  [DecidableEq o]
end Lin
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates


