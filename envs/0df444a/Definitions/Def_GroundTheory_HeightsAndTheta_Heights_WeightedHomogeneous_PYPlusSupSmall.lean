-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSupSmall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:29.775808+00:00
-- url     : https://prove2.me/theorems/50eff4e4-6f2a-4682-bd0c-08f52e5cb5dc
-- title:
--   PYPlus Sup Small
-- statement:
--   Definitions and structural lemmas for PYPlus Sup Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSupSmall.lean

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
namespace YPlusSupSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
def newSubst (g : Fin (D.size + 1) → MvPolynomial (Coord n) ℤ) :
    Coord D.extSizes → MvPolynomial (Coord n) ℤ
  | ⟨none, j⟩ => g j
  | ⟨some _, _⟩ => 0
end YPlusSupSmall
end
end GroundTheory.Heights₂.Heights


