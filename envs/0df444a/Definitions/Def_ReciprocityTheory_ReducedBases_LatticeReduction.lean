-- Prove2me | Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
-- name    : ReciprocityTheory_ReducedBases_LatticeReduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:48.482025+00:00
-- url     : https://prove2.me/theorems/2748fe4a-e41b-435a-b33b-533c102e05a0
-- title:
--   Lattice Reduction
-- statement:
--   Definitions and structural lemmas for Lattice Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/LatticeReduction.lean

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
def IsRed (b : Fin d → E) : Prop :=
  LinearIndependent ℝ b ∧ (∀ i j : Fin d, j < i → |mu b i j| ≤ 1 / 2) ∧
    (∀ i j : Fin d, i.val = j.val + 1 → ‖gs b j‖ ^ 2 ≤ 2 * ‖gs b i‖ ^ 2)
end ReciprocityTheory.ReducedBases.T2
end


