-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:13:19.886892+00:00
-- url     : https://prove2.me/theorems/a136f64c-e135-483b-b4b9-e0548137ada0
-- title:
--   Factor Nonneg
-- statement:
--   Definitions and structural lemmas for Factor Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace GlobalTheory.WigSh.Model
def Box {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) : Prop :=
  ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc
end GlobalTheory.WigSh.Model


