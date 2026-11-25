-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:16:45.631367+00:00
-- url     : https://prove2.me/theorems/78d41db4-ec63-40e9-85e0-16c19c22a340
-- title:
--   Finite Dimensional Base Span
-- statement:
--   Definitions and structural lemmas for Finite Dimensional Base Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FiniteDimensionalBaseSpan.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
noncomputable def incU (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    F ⊗[K] U →ₗ[F] F ⊗[K] V :=
  AlgebraTensorModule.map (LinearMap.id : F →ₗ[F] F) U.subtype
variable {Ω : Type*} [Field Ω] [Algebra K Ω]
noncomputable def fldIncl (K₁ : IntermediateField K Ω) : K₁ →ₗ[K] Ω :=
  (IsScalarTower.toAlgHom K K₁ Ω).toLinearMap
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


