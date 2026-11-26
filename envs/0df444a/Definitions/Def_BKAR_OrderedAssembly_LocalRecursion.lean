-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
-- name    : BKAR_OrderedAssembly_LocalRecursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:53:19.732094+00:00
-- url     : https://prove2.me/theorems/2565ad2f-f7b8-4268-ad1f-03a702964994
-- title:
--   Local Recursion
-- statement:
--   Definitions and structural lemmas for Local Recursion, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean

import Definitions.Def_BKAR_CubePartition_Prefixed
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace ActiveTerminalBranchData
variable {F : Forest V}
noncomputable def localFirstTailRemainder
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  (∫ t in 0..top,
      (data.tail e).branchIntegralAux t
        ((data.extension e).extension.extendParam u t)
        (partialDeriv e.val (mixedPartialList es ρ))) -
    ∫ t in 0..top,
      mixedPartialList (e.val :: es) ρ
        ((data.extension e).forest.interpWithFill
          ((data.extension e).extension.extendParam u t) t)
end ActiveTerminalBranchData
end Forest
end BKAR


