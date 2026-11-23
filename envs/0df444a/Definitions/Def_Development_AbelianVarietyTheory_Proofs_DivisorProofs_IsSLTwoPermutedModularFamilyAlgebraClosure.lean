-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosure
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:36.275445+00:00
-- url     : https://prove2.me/theorems/5e0aaa34-11a2-4910-9b70-2f0b5f94ea5c
-- title:
--   Is SLTwo Permuted Modular Family Algebra Closure
-- statement:
--   Definitions and structural lemmas for Is SLTwo Permuted Modular Family Algebra Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyAlgebraClosure.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
namespace GlobalTheory.QFam
variable {ι : Type} {act : ι → SL(2, ℤ) → ι}
end GlobalTheory.QFam


