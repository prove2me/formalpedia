-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_BetaAtInfinityZero
-- name    : CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_BetaAtInfinityZero
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:08.835934+00:00
-- url     : https://prove2.me/theorems/b572c3f7-bb5e-43ef-8c89-fee0f28ce8bb
-- title:
--   Beta At Infinity Zero
-- statement:
--   Definitions and structural lemmas for Beta At Infinity Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/BetaAtInfinityZero.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk MeasureTheory
open scoped InnerProductSpace
end CompanionTheory.LimBd.Main


