-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:42.261438+00:00
-- url     : https://prove2.me/theorems/82700e4e-5b7c-406b-b74a-f6544224eb94
-- title:
--   PLocally Principal Coprime
-- statement:
--   Definitions and structural lemmas for PLocally Principal Coprime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLocallyPrincipalCoprime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]
open Classical in

noncomputable def toB (B : Subring L) (x : L) : B := if h : x ∈ B then ⟨x, h⟩ else 0
end LocallyPrincipalCoprimeAlt
end GroundTheory.Heights₂.Heights


