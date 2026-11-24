-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:48:03.7702+00:00
-- url     : https://prove2.me/theorems/2f5344e9-31d8-408d-9eb7-c8f083463c7f
-- title:
--   Normal Model Fibre Near
-- statement:
--   Definitions and structural lemmas for Normal Model Fibre Near, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint
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
open MvPolynomial Filter Topology ComplexSets Metric
noncomputable section
namespace NormalModelFibre
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
end NormalModelFibre
end
end GroundTheory.Heights₂.Heights


