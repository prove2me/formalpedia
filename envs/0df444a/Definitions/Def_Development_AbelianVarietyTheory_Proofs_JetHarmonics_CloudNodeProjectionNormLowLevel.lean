-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CloudNodeProjectionNormLowLevel
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_CloudNodeProjectionNormLowLevel
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:43.981817+00:00
-- url     : https://prove2.me/theorems/1a19b4d3-28b1-475e-ab8f-4a6c9c1bbdd7
-- title:
--   Cloud Node Projection Norm Low Level
-- statement:
--   Definitions and structural lemmas for Cloud Node Projection Norm Low Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CloudNodeProjectionNormLowLevel.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterFinBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CardFilterLeSuccAndSqSumLePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormEigenLePowMulNormSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasEigenvalueSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasimirResolventCircleBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LevSubspaceMono
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormSumEigenprojectorLeOfResolventBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
namespace GlobalTheory
end GlobalTheory


