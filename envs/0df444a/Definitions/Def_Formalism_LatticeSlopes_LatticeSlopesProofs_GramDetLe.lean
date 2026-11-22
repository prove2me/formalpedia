-- Prove2me | Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
-- name    : Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:02.069497+00:00
-- url     : https://prove2.me/theorems/4dcf33d0-8a9c-46fb-91f9-5f6fde3a5978
-- title:
--   Gram Det Le
-- statement:
--   Definitions and structural lemmas for Gram Det Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean

import Definitions.Def_Formalism_LatticeSlopes_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.F
def linearCombinationMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun c := ∑ i, c i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]
end Formalism.F


