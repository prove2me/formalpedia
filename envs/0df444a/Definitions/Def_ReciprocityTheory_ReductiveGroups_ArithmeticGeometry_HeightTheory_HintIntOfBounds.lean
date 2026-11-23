-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:23.674274+00:00
-- url     : https://prove2.me/theorems/e76a995b-3905-45b0-9e1e-1dfa91d728f4
-- title:
--   Hint Int Of Bounds
-- statement:
--   Definitions and structural lemmas for Hint Int Of Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights
noncomputable def hintPt {D n : ℕ} (t0 : Fin n → ℂ) (z : BlockSphere D n) :
    Fin (D + 1) × Fin n → ℂ :=
  fun v => Fin.cases (t0 v.2) (fun i => spherePoint (z i) v.2) v.1
end ReciprocityTheory.ChartRestriction.G.T0


