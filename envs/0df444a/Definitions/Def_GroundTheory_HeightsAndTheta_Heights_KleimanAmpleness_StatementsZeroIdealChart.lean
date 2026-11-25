-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsZeroIdealChart
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:29.359098+00:00
-- url     : https://prove2.me/theorems/4f69a308-72d7-5133-9b6c-cd1bc4b821ab
-- title:
--   Statements Zero Ideal Chart
-- statement:
--   Definitions and structural lemmas for Statements Zero Ideal Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsZeroIdealChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
def ZeroIdealChart.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x) (I : Chart x) (y : Ω),
    (∀ δ ∈ T.D.sub I, y * δ ∈ chartRing k x I) → T.si * y ∈ idealMod (x := x) T.J I
end
end GroundTheory.Heights₂.Heights.Kleiman


