-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZColB
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NZColB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:23.049781+00:00
-- url     : https://prove2.me/theorems/5b506fb5-1aec-4de5-ba50-215da2c0e8a1
-- title:
--   NZCol B
-- statement:
--   Definitions and structural lemmas for NZCol B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZColB.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.BasicNotions.Examples₂.NZ
open IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]
def glue (A : HeightOneSpectrum R → Submodule R V) : Submodule R V := ⨅ w, A w
end Formalism.BasicNotions.Examples₂.NZ


