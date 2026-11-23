-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:23.136073+00:00
-- url     : https://prove2.me/theorems/fb9e7642-e866-416f-af9e-4a012e924c98
-- title:
--   Integrable Of Decay VG
-- statement:
--   Definitions and structural lemmas for Integrable Of Decay VG, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrableOfDecayVG.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section ExpB
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
end ExpB
end ReciprocityTheory.ChartRestriction.DS.S7


