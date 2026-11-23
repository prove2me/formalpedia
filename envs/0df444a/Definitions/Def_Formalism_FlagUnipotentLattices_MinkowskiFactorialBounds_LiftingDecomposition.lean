-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:35.687826+00:00
-- url     : https://prove2.me/theorems/03d720b9-2dfd-4797-ad50-fefd6a2a3c91
-- title:
--   Lifting Decomposition
-- statement:
--   Definitions and structural lemmas for Lifting Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LiftingDecomposition.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
namespace Formalism.HermitianLatticeCounting.P
namespace CellDecomposition
section Cell
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
end Cell
end CellDecomposition
open CellDecomposition
namespace CellDecomposition
section Lift
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
def perpL (H : HermSpace K V) (W : Submodule K V) : Submodule K V where
  carrier := {y | ∀ w ∈ W, H.B y w = 0}
  add_mem' := by
    intro a b ha hb w hw
    simp [ha w hw, hb w hw]
  zero_mem' := by intro w _; simp
  smul_mem' := by
    intro c a ha w hw
    simp [ha w hw]
end Lift
end CellDecomposition
end Formalism.HermitianLatticeCounting.P


