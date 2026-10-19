-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_PosteriorMoments
-- name    : OAI_Probability_ThreeState_PosteriorMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:36:04.572605+00:00
-- url     : https://prove2.me/theorems/0285a3df-3a32-4983-a58c-5f8923ee657b
-- title:
--   Deviation of a three-spin message from uniform and its quadratic moment
-- statement:
--   Let $m=(m_0,m_1,m_2)$ be a message: $m_i\ge0$ and $m_0+m_1+m_2=3$.
--
--   1. **Deviation.** $\delta(m)_i=m_i-1$, the deviation of $m$ from the uninformative message $(1,1,1)$.
--   2. **Quadratic moment.**
--   $$
--   X(m)=\frac16\sum_{i=0}^{2}(m_i-1)^2 ,
--   $$
--   that is, half the average of the squared deviations.
--
--   $X(m)$ measures how informative the message is. It is the quantity whose expectation is tracked through the recursion when estimating posterior moments.
--
--   **Formalization Note** `messageX m` is defined as `Radial.momentX (messageDeviation m)`, where `momentX v = avg (v^2) / 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/PosteriorMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/PosteriorMoments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments
import Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives

namespace OAI

/-! Posterior deviation moments and positive-channel estimates. -/

namespace ThreeState
open MeasureTheory Filter Topology
open scoped Classical
open Radial (avg)

noncomputable def messageDeviation (m : Message) : Spin → ℝ := fun i => m i-1
noncomputable def messageX (m : Message) : ℝ := Radial.momentX (messageDeviation m)
 

end ThreeState

end OAI


