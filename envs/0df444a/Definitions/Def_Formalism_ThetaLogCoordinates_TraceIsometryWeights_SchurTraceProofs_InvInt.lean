-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:38.601695+00:00
-- url     : https://prove2.me/theorems/46cba830-a3b9-44b8-b151-e30ae7f84ed7
-- title:
--   Inv Int
-- statement:
--   Definitions and structural lemmas for Inv Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset
section gen
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
def lop (A B : Module.End K W) : Module.End K (Module.End K W) :=
  LinearMap.mulLeft K A * LinearMap.mulRight K B
end gen
section padic
variable {p : ℕ} [Fact p.Prime]
variable {W ι : Type} [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]
end padic
end Formalism.InvariantFactorPaths.PW


