-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryAnnihilator
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryAnnihilator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:11.4088+00:00
-- url     : https://prove2.me/theorems/a254a843-555f-4ca8-a6ae-00c1d4920ce0
-- title:
--   Unitary Annihilator
-- statement:
--   Definitions and structural lemmas for Unitary Annihilator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnitaryAnnihilator.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
section Finite
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
end Finite
section Infinite
variable {F : Type*} [Field F] [NumberField F]
end Infinite
section Adele
variable {F : Type*} [Field F] [NumberField F]
end Adele


