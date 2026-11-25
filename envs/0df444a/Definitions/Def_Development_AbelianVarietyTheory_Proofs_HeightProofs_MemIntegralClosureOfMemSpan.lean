-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:19.2478+00:00
-- url     : https://prove2.me/theorems/55cab3c2-4c72-4d47-bf2b-5e067f37e665
-- title:
--   Mem Integral Closure Of Mem Span
-- statement:
--   Definitions and structural lemmas for Mem Integral Closure Of Mem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
namespace GlobalTheory
namespace PlaceExt
section Abstract
variable {L A : Type*} [Field L] [CommRing A]
variable (ι : L →+* A) (S : Subring A) (π : L) (w : AddValuation L (WithTop ℤ))
end Abstract
section Rings
variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
variable {F F' : Type} [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F']
  [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
  [IsScalarTower R R' F']
variable {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra R L] [IsScalarTower R F L]
end Rings
end PlaceExt
end GlobalTheory


