-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
-- name    : GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:17.324795+00:00
-- url     : https://prove2.me/theorems/7622799f-1ada-4e7e-a938-a29f307fe1ee
-- title:
--   Degree One Primes
-- statement:
--   Definitions and structural lemmas for Degree One Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean

import Mathlib
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
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]
def rationalPrimeUnder (w : HeightOneSpectrum (𝓞 L)) : ℕ :=
  Ideal.absNorm (w.asIdeal.under ℤ)
section relative
variable (K L) [Field K] [NumberField K] [Algebra K L]
def degreeOnePrimes : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | w.asIdeal.inertiaDeg (𝓞 K) = 1}
def higherDegreePrimes : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | 2 ≤ w.asIdeal.inertiaDeg (𝓞 K)}
variable {K L}
end relative
end
end GroundTheory.Global


