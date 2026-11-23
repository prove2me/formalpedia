-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:58.2587+00:00
-- url     : https://prove2.me/theorems/ce60eac6-5ca5-41bc-a84c-993c9cc78e31
-- title:
--   Is Integrally Closed In Fraction Field Power Series
-- statement:
--   Definitions and structural lemmas for Is Integrally Closed In Fraction Field Power Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
namespace GlobalTheory.OnePoint
universe u v w
section Algebra
variable {K : Type u} [Field K]
end Algebra
section Scheme
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]
end Scheme
end GlobalTheory.OnePoint


