-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:58:11.580006+00:00
-- url     : https://prove2.me/theorems/dfd34ef1-b876-44ee-9600-d560b9005187
-- title:
--   Reduction Set Subgroup
-- statement:
--   Definitions and structural lemmas for Reduction Set Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReductionSetSubgroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
namespace GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]
end GlobalTheory.Klein


