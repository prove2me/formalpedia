-- Prove2me | Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
-- name    : ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:27.085077+00:00
-- url     : https://prove2.me/theorems/1fe5c5f4-a18c-4930-8d92-f7bc18237a00
-- title:
--   Norm Gso Comp Swap Right Sq Mul
-- statement:
--   Definitions and structural lemmas for Norm Gso Comp Swap Right Sq Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReducedBases/NormGsoCompSwapRightSqMul.lean

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
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
open Finset InnerProductSpace Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
def pot (b : Fin d → E) : ℝ :=
  ∏ k, ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs b j‖ ^ 2
end ReciprocityTheory.ReducedBases.T2
end


