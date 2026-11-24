-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:18.121649+00:00
-- url     : https://prove2.me/theorems/99b41b36-7331-4742-ba4d-d97321a2e145
-- title:
--   Weyl Int
-- statement:
--   Definitions and structural lemmas for Weyl Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
section gen
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
theorem wl_iso_stable (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) : G.Stable (IsoW G W la) :=
  G.gS_stable _
def topC (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) : IsoW G W la →ₗ[K] V :=
  G.comp la ∘ₗ (IsoW G W la).subtype
end gen
section padic
variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] {n : ℕ}
end padic
end Formalism.InvariantFactorPaths.PW


