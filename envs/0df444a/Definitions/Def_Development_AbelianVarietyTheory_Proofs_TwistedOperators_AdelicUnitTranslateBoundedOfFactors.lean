-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AdelicUnitTranslateBoundedOfFactors
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_AdelicUnitTranslateBoundedOfFactors
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:31:42.619545+00:00
-- url     : https://prove2.me/theorems/b08dea2a-34db-51b2-9cd1-4d534e066eb6
-- title:
--   Adelic Unit Translate Bounded Of Factors
-- statement:
--   Definitions and structural lemmas for Adelic Unit Translate Bounded Of Factors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AdelicUnitTranslateBoundedOfFactors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
namespace GlobalTheory.RegSS
end GlobalTheory.RegSS


