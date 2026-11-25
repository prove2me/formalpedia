-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOne
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:39:06.175873+00:00
-- url     : https://prove2.me/theorems/34658a80-8dbe-45d4-aef5-d3647d540709
-- title:
--   PDiv Group Mul PUnit Fibre Eq Level One
-- statement:
--   Definitions and structural lemmas for PDiv Group Mul PUnit Fibre Eq Level One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOne.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv
namespace GlobalTheory
namespace PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
end PDivGroup
section TensorQuot
variable {R k M : Type} [CommRing R] [CommRing k] [Algebra R k] [AddCommGroup M] [Module R M]
end TensorQuot
namespace PDivGroup
end PDivGroup
end GlobalTheory


