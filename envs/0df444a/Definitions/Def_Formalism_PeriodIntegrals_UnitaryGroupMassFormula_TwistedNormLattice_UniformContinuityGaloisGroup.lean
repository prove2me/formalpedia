-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:18.457932+00:00
-- url     : https://prove2.me/theorems/3347d561-5af1-49e4-bd0d-5e5e99f993e7
-- title:
--   Uniform Continuity Galois Group
-- statement:
--   Definitions and structural lemmas for Uniform Continuity Galois Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
abbrev qE : E := ((Ideal.absNorm P.asIdeal : ℕ) : E)
end PI.TwNormLat.W


