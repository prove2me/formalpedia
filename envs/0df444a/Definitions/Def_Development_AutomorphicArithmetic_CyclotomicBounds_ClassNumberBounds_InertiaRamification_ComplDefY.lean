-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_InertiaRamification_ComplDefY
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_InertiaRamification_ComplDefY
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:50.462945+00:00
-- url     : https://prove2.me/theorems/4c8463fe-4bc6-4132-9401-d4c76aaf934e
-- title:
--   Compl Def Y
-- statement:
--   Definitions and structural lemmas for Compl Def Y, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/InertiaRamification/ComplDefY.lean

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace KStar.Ram
open NumberField IsDedekindDomain IsLocalRing
variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
variable (l : ℕ) [Fact l.Prime] [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})]
end KStar.Ram


