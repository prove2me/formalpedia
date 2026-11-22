-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
-- name    : Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:24.661022+00:00
-- url     : https://prove2.me/theorems/bad3a95f-3574-4375-a6fb-24b6d73eceab
-- title:
--   Substitution Weight Bound
-- statement:
--   Definitions and structural lemmas for Substitution Weight Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
namespace Formalism.DworkPowerSeriesWeights
section General
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]
end General
end Formalism.DworkPowerSeriesWeights


