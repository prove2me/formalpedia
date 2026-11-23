-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:47.140458+00:00
-- url     : https://prove2.me/theorems/cd05e6a9-0df8-4b77-a402-819cb4d4ed5a
-- title:
--   Prime Localization
-- statement:
--   Definitions and structural lemmas for Prime Localization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean

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
open NumberField IsDedekindDomain Polynomial
noncomputable section
variable (L : Type*) [Field L] [NumberField L]
def localizationAt (v : HeightOneSpectrum (𝓞 L)) : Subalgebra (𝓞 L) L :=
  Localization.subalgebra.ofField L v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
variable {L}
instance (v : HeightOneSpectrum (𝓞 L)) : IsLocalization.AtPrime (localizationAt L v) v.asIdeal :=
  Localization.subalgebra.isLocalization_ofField _ _ _
instance (v : HeightOneSpectrum (𝓞 L)) : IsDiscreteValuationRing (localizationAt L v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) v.ne_bot _
end
end GroundTheory.Global


