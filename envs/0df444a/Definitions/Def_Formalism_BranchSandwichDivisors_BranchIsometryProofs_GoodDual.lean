-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
-- name    : Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:54.529802+00:00
-- url     : https://prove2.me/theorems/9b38d6c5-0c53-4fa8-ba61-af81a277fa9a
-- title:
--   Good Dual
-- statement:
--   Definitions and structural lemmas for Good Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/GoodDual.lean

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.BranchingDeterminantCap
namespace GoodDualLattice
section
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
def tw (g : V →ₗ⋆[K] K) : V →ₗ[K] K where
  toFun y := star (g y)
  map_add' a b := by simp
  map_smul' k y := by simp [starRingEnd_apply]
end
end GoodDualLattice
end Formalism.BranchingDeterminantCap


