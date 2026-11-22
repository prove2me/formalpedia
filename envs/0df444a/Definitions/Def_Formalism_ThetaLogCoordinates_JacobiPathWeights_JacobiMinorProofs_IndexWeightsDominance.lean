-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:28.298124+00:00
-- url     : https://prove2.me/theorems/17f0f145-eff9-494c-988c-d2bc5c169989
-- title:
--   Index Weights Dominance
-- statement:
--   Definitions and structural lemmas for Index Weights Dominance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IndexWeightsDominance.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A3comb
end A3comb
namespace A3comb
def rowsLt (n j : ℕ) : Finset (Fin n) := univ.filter fun m => m.val < j
end A3comb
namespace A3comb
def mkMon {n N : ℕ} (d : Fin N → (Fin n →₀ ℕ)) : ℕ × Fin n →₀ ℕ :=
  Finsupp.onFinset (range N ×ˢ univ) (fun x => if h : x.1 < N then d ⟨x.1, h⟩ x.2 else 0) (by
    intro x hx
    rw [Finset.mem_product, Finset.mem_range]
    refine ⟨?_, Finset.mem_univ _⟩
    by_contra h
    exact hx (dif_neg h))
end A3comb
namespace A3comb
end A3comb
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


