-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelGoodPointChart
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelGoodPointChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:57:26.934898+00:00
-- url     : https://prove2.me/theorems/faa6bc8d-50a4-4e41-b45a-6a6e89f11051
-- title:
--   St Normal Model Good Point Chart
-- statement:
--   Definitions and structural lemmas for St Normal Model Good Point Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelGoodPointChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDivisorChartGeneric
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
open MvPolynomial ComplexSets
noncomputable section
def NormalModelGoodPointChart.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ), NormalModelDivisorGoodPoint M u d w → NormalDivisorChartAtPoint M u d w
end
end GroundTheory.Heights₂.Heights


