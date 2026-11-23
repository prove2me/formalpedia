-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:21.172812+00:00
-- url     : https://prove2.me/theorems/a92e43ca-5cb8-4f55-9558-de833a8f5c31
-- title:
--   Mul Vec Span Stable
-- statement:
--   Definitions and structural lemmas for Mul Vec Span Stable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/MulVecSpanStable.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.LevelKSplit.W.Loc
open Submodule
variable {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n r : ℕ}
def dl (c : Fin n → B) : (Fin n → B) →ₗ[B] B where
  toFun y := c ⬝ᵥ y
  map_add' x y := dotProduct_add c x y
  map_smul' a y := by simp [dotProduct_smul]
end PI.LevelKSplit.W.Loc


