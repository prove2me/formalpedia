-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:59.137902+00:00
-- url     : https://prove2.me/theorems/f12cd4e2-805f-4d2d-b1d8-5fe11eb37c14
-- title:
--   Schur Trace Of Hom Inv
-- statement:
--   Definitions and structural lemmas for Schur Trace Of Hom Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/SchurTraceOfHomInv.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity
section gen
variable {K V V₁ V₂ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂] {n : ℕ}
def mapsInto (V₁ : Type) [AddCommGroup V₁] [Module K V₁] (W : Submodule K V₂) : Submodule K (V₁ →ₗ[K] V₂) where
  carrier := {φ | ∀ x, φ x ∈ W}
  add_mem' := fun {φ ψ} hφ hψ x => by rw [LinearMap.add_apply]; exact W.add_mem (hφ x) (hψ x)
  zero_mem' := fun x => by rw [LinearMap.zero_apply]; exact W.zero_mem
  smul_mem' := fun c φ hφ x => by rw [LinearMap.smul_apply]; exact W.smul_mem c (hφ x)
end gen
end Formalism.InvariantFactorPaths.PW


