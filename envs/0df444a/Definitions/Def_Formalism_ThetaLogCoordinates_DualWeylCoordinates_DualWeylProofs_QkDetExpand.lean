-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:31.042061+00:00
-- url     : https://prove2.me/theorems/ca5adb83-228d-47df-87c7-763db96dd100
-- title:
--   Qk Det Expand
-- statement:
--   Definitions and structural lemmas for Qk Det Expand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QkDetExpand.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def qk_D {n : ℕ} (v : Fin n → ℝ) : ℝ := ∏ i : Fin n, ∏ j ∈ Ioi i, (v j - v i)
end Formalism.InvariantFactorPaths.ColumnFamilies


