-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicCompactDensity_ExistsNatLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:23.225802+00:00
-- url     : https://prove2.me/theorems/9eb1a43d-2e54-4dd7-b10a-984ca2182bb8
-- title:
--   Exists Nat Local
-- statement:
--   Definitions and structural lemmas for Exists Nat Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicCompactDensity/ExistsNatLocal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.AdCpctDenWork
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]
def intAd (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}
end PI.AdCpctDenWork


