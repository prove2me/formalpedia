-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSec
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:47.604613+00:00
-- url     : https://prove2.me/theorems/365da0f6-d2c8-46f8-97d5-c7d5f34a182f
-- title:
--   PYPlus Sec
-- statement:
--   Definitions and structural lemmas for PYPlus Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSec.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
namespace YPlusSec
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
def newEmb : (Σ _ : Unit, Fin (D.size + 1)) → Coord D.extSizes := fun p ↦ ⟨none, p.2⟩
end YPlusSec
end
end GroundTheory.Heights₂.Heights


