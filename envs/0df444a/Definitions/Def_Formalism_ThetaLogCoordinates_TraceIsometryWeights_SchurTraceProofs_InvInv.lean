-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:40.135396+00:00
-- url     : https://prove2.me/theorems/e8d34b12-de12-41f1-8459-eb2396cd42ee
-- title:
--   Inv Inv
-- statement:
--   Definitions and structural lemmas for Inv Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInv.lean

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
section nat
variable {K W W' ι : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] [DecidableEq ι]
end nat
section ring
variable {R : Type} [Ring R]
end ring
section gl
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
def Cj (E : ι → ι → Module.End K W) (S : Finset ι) (z j : ι) : Module.End K W :=
  ∑ i ∈ S, E i z * E j i - E j z * E z z + ((S.card : K) + 1) • E j z
def cc (K : Type) [Field K] (m q : ℕ) : K :=
  ((-1 : K) ^ q * (m.factorial : K)) / (((q + m).factorial : K) * (q.factorial : K))
end gl
end Formalism.InvariantFactorPaths.PW


