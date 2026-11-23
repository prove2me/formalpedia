-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_InertPrimesSquareNorm
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_InertPrimesSquareNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:58.61762+00:00
-- url     : https://prove2.me/theorems/a4186921-e5a6-4219-913f-d237c27e8b12
-- title:
--   Inert Primes Square Norm
-- statement:
--   Definitions and structural lemmas for Inert Primes Square Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/InertPrimesSquareNorm.lean

import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLemma₂
open NumberField IsDedekindDomain
def InertPrimesSquareNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal)
end Formalism.MainNotions.BridgeLemma₂
end


