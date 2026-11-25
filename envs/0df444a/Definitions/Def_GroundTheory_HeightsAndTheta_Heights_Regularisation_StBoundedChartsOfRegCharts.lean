-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StBoundedChartsOfRegCharts
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_StBoundedChartsOfRegCharts
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:07:05.435925+00:00
-- url     : https://prove2.me/theorems/df9ade0b-88f3-53bd-bdb5-b0f152e03baa
-- title:
--   St Bounded Charts Of Reg Charts
-- statement:
--   Definitions and structural lemmas for St Bounded Charts Of Reg Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/StBoundedChartsOfRegCharts.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ProjLineChartsNotSubsetBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open Metric
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
def BoundedChartsOfRegCharts.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegCharts A) (P : BoundedThPsh R),
    ∃ Q : GroundTheory.Heights₂.Heights.Regular.BoundedPshData A, Q.ph = P.φ ∧ Q.th = R.θ
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular


