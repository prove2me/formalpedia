-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdeleCongruenceUnitCriterion
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdeleCongruenceUnitCriterion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:15.080823+00:00
-- url     : https://prove2.me/theorems/7071c234-1b6d-42f1-bed1-ae246355b0cd
-- title:
--   Idele Congruence Unit Criterion
-- statement:
--   Definitions and structural lemmas for Idele Congruence Unit Criterion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdeleCongruenceUnitCriterion.lean

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
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors Topology
namespace GlobalTheory.IdeleCharLevel
variable (K : Type) [Field K] [NumberField K]
end GlobalTheory.IdeleCharLevel


