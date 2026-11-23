-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinNonconstantTermsHasSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinNonconstantTermsHasSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:32.043631+00:00
-- url     : https://prove2.me/theorems/e9e12fe4-390e-45df-a795-e0a304171bb9
-- title:
--   Hilbert Eisenstein Nonconstant Terms Has Sum
-- statement:
--   Definitions and structural lemmas for Hilbert Eisenstein Nonconstant Terms Has Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinNonconstantTermsHasSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivLatticeClassesFibreSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummandStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeSumEqConeSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
noncomputable section
namespace GlobalTheory.EisNonConst
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
end GlobalTheory.EisNonConst


