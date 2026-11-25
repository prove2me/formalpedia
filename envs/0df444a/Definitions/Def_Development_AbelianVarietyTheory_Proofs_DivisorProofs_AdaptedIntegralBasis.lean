-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:52:39.16229+00:00
-- url     : https://prove2.me/theorems/ceae161f-28e9-421b-88c4-0caf514c91e2
-- title:
--   Adapted Integral Basis
-- statement:
--   Definitions and structural lemmas for Adapted Integral Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdaptedIntegralBasis.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
namespace GlobalTheory.LaurentFlagBasis
variable {F : Type} [Field F]
noncomputable def red {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → F := fun a => constantCoeff (y a)
noncomputable def lift {n : ℕ} (y : Fin n → PowerSeries F) : Fin n → LaurentSeries F :=
  fun a => (y a : LaurentSeries F)
end GlobalTheory.LaurentFlagBasis


