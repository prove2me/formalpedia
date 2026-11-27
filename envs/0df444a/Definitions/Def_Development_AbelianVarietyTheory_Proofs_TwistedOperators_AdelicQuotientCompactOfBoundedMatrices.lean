-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AdelicQuotientCompactOfBoundedMatrices
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_AdelicQuotientCompactOfBoundedMatrices
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:30:07.034946+00:00
-- url     : https://prove2.me/theorems/92da7720-38af-52d7-a591-07ac50bdd24a
-- title:
--   Adelic Quotient Compact Of Bounded Matrices
-- statement:
--   Definitions and structural lemmas for Adelic Quotient Compact Of Bounded Matrices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/AdelicQuotientCompactOfBoundedMatrices.lean

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
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct
namespace GlobalTheory.RegSS.CptQuot
end GlobalTheory.RegSS.CptQuot


