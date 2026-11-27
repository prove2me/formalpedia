-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T06:19:23.762699+00:00
-- url     : https://prove2.me/theorems/2448d09b-707b-5d02-9aa9-c2d3a675c94d
-- title:
--   Regular Semisimple Tensor Commutant
-- statement:
--   Definitions and structural lemmas for Regular Semisimple Tensor Commutant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean

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
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
namespace GlobalTheory.RegSS
section Columns
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
def colMat (c : n → Matrix n n A) (v : n → A) : Matrix n n A :=
  Matrix.of fun i j => (c j *ᵥ v) i
end Columns
end GlobalTheory.RegSS


