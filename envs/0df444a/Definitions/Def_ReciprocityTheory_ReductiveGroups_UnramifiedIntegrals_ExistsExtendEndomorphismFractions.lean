-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:11.427797+00:00
-- url     : https://prove2.me/theorems/7d5abf57-c800-4f82-a634-d2d20183d3d4
-- title:
--   Exists Extend Endomorphism Fractions
-- statement:
--   Definitions and structural lemmas for Exists Extend Endomorphism Fractions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ExistsExtendEndomorphismFractions.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
section Generic
variable {K : Type*} [Field K] (R : Subring K) (F : Subfield K) (h : R ≤ F.toSubring)
def subringInclusionSubfield : R →+* F := Subring.inclusion h
end Generic
end ReciprocityTheory.ChartRestriction.L1


