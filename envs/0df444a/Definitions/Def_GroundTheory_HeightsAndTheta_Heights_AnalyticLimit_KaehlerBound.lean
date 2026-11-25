-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_KaehlerBound
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_KaehlerBound
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:25:17.30063+00:00
-- url     : https://prove2.me/theorems/867ad29e-8c75-5e13-ac2d-c8396625eb97
-- title:
--   Kaehler Bound
-- statement:
--   Definitions and structural lemmas for Kaehler Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/KaehlerBound.lean

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData projLineChartData)
def KaehlerBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (R : RegChartData A),
    ∃ Om : KaehlerForm A, LeviLe A Set.univ 1 (thetaOmega R) 1 Om.pot ∧
      LeviLe A Set.univ (-1) Om.pot 1 (thetaOmega R)
end GroundTheory.Heights₂.Heights.AnalyticLimit


