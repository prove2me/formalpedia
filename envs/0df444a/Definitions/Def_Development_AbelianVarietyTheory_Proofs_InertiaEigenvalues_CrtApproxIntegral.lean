-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegral
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:09:30.434842+00:00
-- url     : https://prove2.me/theorems/a6a6134f-a16f-4328-b31b-46d03eb22f05
-- title:
--   Crt Approx Integral
-- statement:
--   Definitions and structural lemmas for Crt Approx Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrtApproxIntegral.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
namespace GlobalTheory
end GlobalTheory


