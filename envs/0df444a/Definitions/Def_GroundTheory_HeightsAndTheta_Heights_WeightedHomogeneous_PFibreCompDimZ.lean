-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PFibreCompDimZ
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PFibreCompDimZ
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:07:54.932859+00:00
-- url     : https://prove2.me/theorems/8779e222-e621-5346-81fa-275cc9dde952
-- title:
--   PFibre Comp Dim Z
-- statement:
--   Definitions and structural lemmas for PFibre Comp Dim Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PFibreCompDimZ.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsFibreCompDimZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfChartPointSecPointSpecChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial IsDedekindDomain
section Fibres
variable {σ : Type} [Fintype σ] {P : Ideal (MvPolynomial σ ℤ)}
end Fibres
end GroundTheory.Heights₂.Heights


