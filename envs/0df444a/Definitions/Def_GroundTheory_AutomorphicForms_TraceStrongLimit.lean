-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
-- name    : GroundTheory_AutomorphicForms_TraceStrongLimit
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:12.16796+00:00
-- url     : https://prove2.me/theorems/b4fb265c-8977-46e5-876b-89f890cd8680
-- title:
--   Trace Strong Limit
-- statement:
--   Definitions and structural lemmas for Trace Strong Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
section FinProj
variable {ι : Type*} [Fintype ι]
def finProj (u : ι → H) : H →L[ℂ] H := ∑ i, rankOne ℂ (u i) (u i)
variable {u : ι → H}
end FinProj
section Limits
variable [CompleteSpace H]
end Limits
end
end GroundTheory.Automorphic


