-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:51:12.14218+00:00
-- url     : https://prove2.me/theorems/e26dd8f9-628d-5177-a6bf-3a0bc96800eb
-- title:
--   Is Smooth Metric Of Is Smooth Herm
-- statement:
--   Definitions and structural lemmas for Is Smooth Metric Of Is Smooth Herm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsSmoothMetricOfIsSmoothHerm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


