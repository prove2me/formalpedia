-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:05.802104+00:00
-- url     : https://prove2.me/theorems/91e7f37a-299f-4fb3-ab7e-39e0c978de64
-- title:
--   Cas KHW
-- statement:
--   Definitions and structural lemmas for Cas KHW, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CasKHW.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
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
def casKHW_coef {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a b : Fin n) : ℝ :=
  if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0) else 0
end Formalism.REAL


