-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:25.402465+00:00
-- url     : https://prove2.me/theorems/91c39f8a-0989-4568-b12e-55a1aa41142a
-- title:
--   Finite Algebra Local Completion
-- statement:
--   Definitions and structural lemmas for Finite Algebra Local Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteAlgebraLocalCompletion.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
open IsLocalRing Polynomial
section
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (L : Type*) [Field L] [Algebra R L] [FaithfulSMul R L] [Module.Finite R (integralClosure R L)]
end
section
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
include K
variable [Module.Finite R (integralClosure R L)]
end
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion


