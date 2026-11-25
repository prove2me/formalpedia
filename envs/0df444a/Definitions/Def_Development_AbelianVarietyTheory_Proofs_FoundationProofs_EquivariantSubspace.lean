-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EquivariantSubspace
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_EquivariantSubspace
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:13.554398+00:00
-- url     : https://prove2.me/theorems/ee6f0795-b52d-4d13-8f7e-93c05d007549
-- title:
--   Equivariant Subspace
-- statement:
--   Definitions and structural lemmas for Equivariant Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EquivariantSubspace.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.QuantumDeterminants
namespace GlobalTheory.EquivariantSubspace
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end GlobalTheory.EquivariantSubspace


