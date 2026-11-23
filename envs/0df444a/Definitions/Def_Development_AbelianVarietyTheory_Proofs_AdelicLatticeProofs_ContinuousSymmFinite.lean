-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousSymmFinite
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousSymmFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:22.102583+00:00
-- url     : https://prove2.me/theorems/e40a5b59-1218-4df3-8c3c-90c60369e56a
-- title:
--   Continuous Symm Finite
-- statement:
--   Definitions and structural lemmas for Continuous Symm Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ContinuousSymmFinite.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open scoped Topology
namespace GlobalTheory.AdeleBaseChange
end GlobalTheory.AdeleBaseChange


