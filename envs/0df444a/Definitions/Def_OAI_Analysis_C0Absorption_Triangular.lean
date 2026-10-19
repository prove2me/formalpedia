-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Triangular
-- name    : OAI_Analysis_C0Absorption_Triangular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:02:19.32237+00:00
-- url     : https://prove2.me/theorems/df79eaac-267b-44b7-bfd4-c03623f1ead6
-- title:
--   Absorption maps and radial lifts
-- statement:
--   Let $E$, $U$ and $Z$ be real normed spaces.
--
--   1. **Absorption map.** For a continuous linear map $Q:Z\to U$ and a map $K:E\times U\to Z$,
--   $$
--   \mathrm{absorptionMap}(Q,K)(x,e)=x+K(e,Qx),\qquad(x,e)\in Z\times E .
--   $$
--   It is triangular: the $Z$-component is shifted by a correction depending on $e$ and on the coordinates $Qx$. When $K$ is Lipschitz and suitably small in the $U$-variable, such maps are bi-Lipschitz.
--   2. **Normalization.** $\mathrm{normalize}(x)=x/\|x\|$ (and $0\mapsto0$) lands in the closed unit ball.
--   3. **Radial lift.** For a map $\zeta$ from the closed unit ball of $E$ to $Z$, $\mathrm{radialLift}(\zeta)(x)=\|x\|\,\zeta(x/\|x\|)$ extends $\zeta$ positively homogeneously to all of $E$, with value $0$ at $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Triangular.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Triangular.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

open Set Filter Topology
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E U Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def absorptionMap (Q : Z →L[ℝ] U) (K : E × U → Z) (x : Z × E) : Z :=
  x.1 + K (x.2, Q x.1)

end
end C0Absorption

open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem normalize_norm_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (norm_normalize hx).le

def normalizedBall (x : E) : Metric.closedBall (0 : E) 1 :=
  ⟨normalize x, by simpa only [Metric.mem_closedBall, dist_zero_right] using normalize_norm_le_one x⟩

def zeroBall : Metric.closedBall (0 : E) 1 := ⟨0, by simp⟩

@[simp] theorem normalizedBall_zero : normalizedBall (0 : E) = zeroBall := by
  apply Subtype.ext
  simp [normalizedBall, zeroBall]

def radialLift (ζ : Metric.closedBall (0 : E) 1 → Z) (x : E) : Z :=
  ‖x‖ • ζ (normalizedBall x)

@[simp] theorem radialLift_zero (ζ : Metric.closedBall (0 : E) 1 → Z) : radialLift ζ 0 = 0 := by
  simp [radialLift]

end
end C0Absorption

end OAI


