-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:03.209768+00:00
-- url     : https://prove2.me/theorems/5ef29aa7-5029-428f-ba99-cf9aa1c63b97
-- title:
--   Lattice Data Counting
-- statement:
--   Definitions and structural lemmas for Lattice Data Counting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LatticeDataCounting.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
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
open NumberField
namespace Formalism.HermitianLatticeCounting.P
namespace LatticeDataCounting
section Lat
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
end Lat
section Dual
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U]
def hdualSub (h : U →ₗ[E] U →ₗ⋆[E] E) (N : Submodule (𝓞 E) U) : Submodule (𝓞 E) U :=
  { hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup with
    smul_mem' := by
      intro a x hx y hy
      rw [← algebraMap_smul E a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact (algebraMap (𝓞 E) E).range.mul_mem ⟨a, rfl⟩ (hx y hy) }
end Dual
end LatticeDataCounting
end Formalism.HermitianLatticeCounting.P


