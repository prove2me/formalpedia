-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
-- name    : GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:54.237893+00:00
-- url     : https://prove2.me/theorems/728b8a2b-bfac-408c-ad21-eeb53667368a
-- title:
--   Degree One Density
-- statement:
--   Definitions and structural lemmas for Degree One Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
section density
variable {K : Type*} [Field K] [NumberField K]
end density
section degreeOne
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
end degreeOne
section asymptotic
variable (K : Type*) [Field K] [NumberField K]
end asymptotic
section split
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
def primesAbove (T : Set (HeightOneSpectrum (𝓞 K))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | w.under (𝓞 K) ∈ T}
end split
section relation
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
end relation
section chebotarevSplit
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
end chebotarevSplit
end
end GroundTheory.Global


