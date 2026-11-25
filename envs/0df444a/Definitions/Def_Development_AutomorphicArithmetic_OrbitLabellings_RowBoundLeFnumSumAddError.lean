-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowBoundLeFnumSumAddError
-- name    : Development_AutomorphicArithmetic_OrbitLabellings_RowBoundLeFnumSumAddError
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:32:56.638802+00:00
-- url     : https://prove2.me/theorems/d97a68e9-930d-4dc0-bbf7-ccb6d3b620ee
-- title:
--   Row Bound Le Fnum Sum Add Error
-- statement:
--   Definitions and structural lemmas for Row Bound Le Fnum Sum Add Error, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/RowBoundLeFnumSumAddError.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowDefs
import Definitions.Def_Formalism_DropLevelBounds_ThBounds
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_AttainsBlockListOfWeightsAlongOrbits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MulFlowValLe
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2
namespace UpperTheory.G2.RowBd
open Formalism.L2.FormalSeriesBounds.RF (i0 blockBd chBd Windows)
structure Plan (l d : ℕ) [NeZero d] (W : ZMod d → ℕ) where
  y : ZMod d → ℕ → ℕ
  u : ZMod d → ℕ
  supp : ∀ a i, i ∉ oddLevels d → y a i = 0
  bal : ∀ a, W a = (∑ i ∈ oddLevels d, l ^ i * y a i) + (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) + u a
noncomputable def Plan.bound {l d : ℕ} [NeZero d] {W : ZMod d → ℕ} (p : Plan l d W) (n m : ℕ) : ℝ :=
  (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (p.y a i)) + ∑ a, chBd l n m (p.u a)
section
variable {l d : ℕ} [NeZero d]
end
end UpperTheory.G2.RowBd


