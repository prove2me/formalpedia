-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:42.035901+00:00
-- url     : https://prove2.me/theorems/b285a394-0a5e-4aa7-9a86-7b883e1bd555
-- title:
--   Tr Pow Sum Filter Zero
-- statement:
--   Definitions and structural lemmas for Tr Pow Sum Filter Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/TrPowSumFilterZero.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
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
namespace Formalism.REAL
def TrPow_m {n : ℕ} (l : Fin n → ℂ) : ℕ → Fin n → ℂ
  | 0 => fun _ => 1
  | k + 1 => fun a => l a * TrPow_m l k a - ∑ b ∈ univ.filter (fun b => a < b), TrPow_m l k b
end Formalism.REAL


