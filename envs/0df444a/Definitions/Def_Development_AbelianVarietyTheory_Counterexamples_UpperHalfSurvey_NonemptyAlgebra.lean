-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_NonemptyAlgebra
-- name    : Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_NonemptyAlgebra
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:49:24.961068+00:00
-- url     : https://prove2.me/theorems/b409d0ea-2a2a-4db8-9fdf-868c5d865518
-- title:
--   Nonempty Algebra
-- statement:
--   Definitions and structural lemmas for Nonempty Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/NonemptyAlgebra.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WittVector Ideal ReciprocityTheory.PGsh
namespace GlobalTheory.AinfChecks
section
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
end
end GlobalTheory.AinfChecks


