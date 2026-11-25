-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Dorbit
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Dorbit
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:08:29.982291+00:00
-- url     : https://prove2.me/theorems/da88f604-05a8-4491-ab00-b0d8407fae94
-- title:
--   Dorbit
-- statement:
--   Definitions and structural lemmas for Dorbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Dorbit.lean

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
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
namespace GlobalTheory.LocalExtField
open Polynomial
end GlobalTheory.LocalExtField


