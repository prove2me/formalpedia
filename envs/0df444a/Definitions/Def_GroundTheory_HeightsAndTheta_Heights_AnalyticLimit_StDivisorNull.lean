-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_StDivisorNull
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_StDivisorNull
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:14:04.902591+00:00
-- url     : https://prove2.me/theorems/e8f2339c-dbc3-588c-a567-0d69becee3bf
-- title:
--   St Divisor Null
-- statement:
--   Definitions and structural lemmas for St Divisor Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/StDivisorNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
def DivisorNull.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (R : RegChartData A),
    A.IsAnalyticSubset R.Yoᶜ ∧ interior R.Yoᶜ = ∅
end GroundTheory.Heights₂.Heights.AnalyticLimit


