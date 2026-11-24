-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:29.573333+00:00
-- url     : https://prove2.me/theorems/3afa98ef-69b5-4ea5-84d5-0251a5c16e28
-- title:
--   PTwin Eq Bundle Local
-- statement:
--   Definitions and structural lemmas for PTwin Eq Bundle Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwinEqBundleLocal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open scoped Pointwise
variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
section Local
variable (A : Subalgebra S Ω) {k : ℕ} (f c : Fin k → Ω)
end Local
section Lift
variable {A B : Subalgebra S Ω}
end Lift
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq


