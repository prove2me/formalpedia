-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartDivisorLength
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartDivisorLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:14.779614+00:00
-- url     : https://prove2.me/theorems/30efa53a-ac5f-4035-a56d-8219d1bfa55a
-- title:
--   PChart Divisor Length
-- statement:
--   Definitions and structural lemmas for PChart Divisor Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartDivisorLength.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisorLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDivisorComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSectionLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLocalSectionLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPiQuotCokerFiniteLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn divSupp IsHorizontal multAt mcPts)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents localMult mem_segreChartComponents)
variable {K : Type*} [Fintype K] {ι : K → Type*}
end GroundTheory.Heights₂.Heights.Targets


