-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_Imports
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:09:52.16615+00:00
-- url     : https://prove2.me/theorems/7b797b13-cad5-4177-ac23-b5ed186faef4
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/Imports.lean

import Mathlib
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
namespace GlobalTheory.WigSh
def wP {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) (l : Fin (n + 1)) : ℝ :=
  (∏ j, ((M j : ℝ) - 1 - (L l : ℝ))) / ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))
def wM {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) (l : Fin (n + 1)) : ℝ :=
  (∏ j, ((M j : ℝ) - (L l : ℝ))) / ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))
end GlobalTheory.WigSh


