-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentraliserPointsBoundedOfNormOneBounded
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentraliserPointsBoundedOfNormOneBounded
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-27T06:28:55.70682+00:00
-- url     : https://prove2.me/theorems/6c500538-fa36-4cbe-9853-d44da43c5bf6
-- title:
--   Centraliser Points Bounded Of Norm One Bounded
-- statement:
--   Definitions and structural lemmas for Centraliser Points Bounded Of Norm One Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CentraliserPointsBoundedOfNormOneBounded.lean

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
namespace GlobalTheory.RegSS.MatBd
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
def entry (σ : E →ₐ[F] E) (J γ : Matrix n n E) (i j : n) : plusAlg σ J γ ⊗[F] E →ₗ[F] E where
  toFun x := (plusTensor σ J γ x : Matrix n n E) i j
  map_add' a b := by rw [map_add]; rfl
  map_smul' c a := by rw [map_smul]; rfl
end GlobalTheory.RegSS.MatBd


