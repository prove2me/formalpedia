-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_FunctionFieldIntegral
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_FunctionFieldIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:09.821809+00:00
-- url     : https://prove2.me/theorems/0ac22a78-a0bc-4bf4-af52-7522436c358c
-- title:
--   Function Field Integral
-- statement:
--   Definitions and structural lemmas for Function Field Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/FunctionFieldIntegral.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
noncomputable section
def functionFieldCongr {F : Type*} [Field F] {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.FunctionField ≃+* V'.toAffine.FunctionField := by
  subst h
  exact RingEquiv.refl _
variable {L : Type*} [Field L] [NumberField L]
end
end GroundTheory.Global


