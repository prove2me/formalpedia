-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
-- name    : OAI_Combinatorics_HoneycombCorridor_CollisionPhase
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:39:51.64331+00:00
-- url     : https://prove2.me/theorems/c02983e2-e768-48dc-95b2-ad867d920347
-- title:
--   The collision phase identity for simple closed honeycomb walks
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns.
--
--   1. **Unused slot.** At a germ $g$ with chosen turn $b$, the unused slot is the outgoing slot of the opposite turn.
--   2. **Turn units and weights.** $\mathrm{turnUnits}$ is additive under concatenation, negated by reversal, and
--   $$
--   \mathrm{wordWeight}(w)=\lambda^{|w|}\exp\Bigl(i\,\frac\pi8\,\mathrm{turnUnits}(w)\Bigr).
--   $$
--   3. **CollisionPhase.** This proposition says the following. Let $b::w$ be a simple closed walk from $g$ whose word flow is represented by an indicator potential $p$ with values in $\{0,\varepsilon\}$, $\varepsilon=\pm1$. Then the two words obtained by switching the first turn and by reversing the loop after the first turn satisfy
--   $$
--   \mathrm{wordWeight}(\bar b::w)+\mathrm{wordWeight}(b::\mathrm{reverseTurns}\,w)=\begin{cases}0,&p(\text{face of the unused slot})=0,\\-2\lambda^{|w|+1},&\text{otherwise.}\end{cases}
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionPhase.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionPhase.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def unusedSlot (g : Germ) (b : Bool) : Fin 3 := outgoingSlot g (!b)

@[simp] theorem turnUnit_not (b : Bool) : turnUnit (!b) = -turnUnit b := by
  cases b <;> simp [turnUnit]

@[simp] theorem turnUnits_cons (b : Bool) (w : List Bool) :
    turnUnits (b :: w) = turnUnit b + turnUnits w := by
  simp [turnUnits]

@[simp] theorem turnUnits_reverse (w : List Bool) :
    turnUnits (reverseTurns w) = -turnUnits w := by
  simp [turnUnits,reverseTurns,List.map_map,Function.comp_def,List.sum_neg]

@[simp] theorem wordWeight_append (u w : List Bool) :
    wordWeight (u ++ w) = wordWeight u * wordWeight w := by
  simp [wordWeight]

theorem turnAngle_sum (w : List Bool) :
    (w.map turnAngle).sum = (Real.pi / 3) * (turnUnits w : ℝ) := by
  induction w with
  | nil => simp [turnUnits]
  | cons b w ih =>
      simp only [List.map_cons,List.sum_cons,ih,turnUnits_cons,Int.cast_add]
      cases b <;> simp [turnAngle,turnUnit] <;> ring

theorem wordWeight_turnUnits (w : List Bool) :
    wordWeight w = (criticalActivity : ℂ) ^ w.length *
      Complex.exp (((Real.pi / 8) * (turnUnits w : ℝ) : ℝ) * Complex.I) := by
  rw [wordWeight_physical,turnAngle_sum]
  congr 2
  push_cast
  ring

def CollisionPhase : Prop := ∀ (g : Germ) (b : Bool) (w : List Bool)
  (p : FaceIndex →₀ ℤ) (ε : ℤ),
  (traced g (b :: w)).Nodup → terminalGerm g (b :: w) = g →
  RepresentsFlow p (wordFlow g (b :: w)) → p ≠ 0 →
  (ε = 1 ∨ ε = -1) → (∀ a, p a = 0 ∨ p a = ε) →
  wordWeight ((!b) :: w) + wordWeight (b :: reverseTurns w) =
    if p (leftFace (g.1,unusedSlot g b)) = 0 then 0
    else -2 * (criticalActivity : ℂ) ^ (b :: w).length

end PolynomialVacuumBridge.Corridor

end

end OAI


