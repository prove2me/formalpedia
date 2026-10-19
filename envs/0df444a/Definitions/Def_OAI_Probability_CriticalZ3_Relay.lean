-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Relay
-- name    : OAI_Probability_CriticalZ3_Relay
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:18:31.150494+00:00
-- url     : https://prove2.me/theorems/a1ae128c-25de-4c0f-bb56-7bd37d745714
-- title:
--   Rectangles, quarter-faces and the relay route in Z³
-- statement:
--   Geometric regions in $\mathbb Z^3$ used to relay a connection from a cube to a neighbouring cube.
--
--   1. **Rectangles.** $\mathrm{Rect}(c,w)=\{x:\ |x_i-c_i|\le w_i\}$; cubes have equal widths, and expanding adds $R$ to every width.
--   2. **Quarter-faces.** For a centre $u$, size $s$, normal coordinate $h$ and signs, the quarter-face lies in the plane $x_h=u_h\pm s$ and, in each other coordinate $i$, in $[u_i,u_i+s]$ or $[u_i-s,u_i]$. The inward signs point towards the origin.
--   3. **The prism and route.** The prism is
--   $$
--   \{x:\ -10r\le x_0\le30r+1,\ |x_1|,|x_2|\le10r\}.
--   $$
--   The route is a sequence of rectangles $P_i$: for $i\le3$ centred at $0$ with contracting widths, then centred at $(2r(i-3),0,0)$ for $i\le12$, and finally at $(20r+1,0,0)$, with widths growing by $R$ per step. $P_0$ is the cube of radius $4r$, and the step size is $2r$ or $2r+1$.
--   4. **Interfaces.** A region has an interface towards $T$ if every point $u$ of its $R$-expansion is the centre of a cube of size $s\in\{2r,2r+1,10r\}$ inside the prism with some quarter-face contained in $T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Relay.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Relay.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CriticalZ3 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace LatticeRelay
open Set
abbrev Vertex := Fin 3 → ℤ

def Rect (c w : Vertex) : Set Vertex := {x | ∀ i, |x i - c i| ≤ w i}
def Cube (c : Vertex) (s : ℤ) : Set Vertex := Rect c (fun _ => s)
def Expand (c w : Vertex) (R : ℤ) : Set Vertex := Rect c (fun i => w i + R)
def DirectedInterval (a s : ℤ) (positive : Bool) (b : ℤ) : Prop :=
  if positive then a ≤ b ∧ b ≤ a+s else a-s ≤ b ∧ b ≤ a

def QuarterFace (u : Vertex) (s : ℤ) (normal : Fin 3) (signs : Fin 3 → Bool) : Set Vertex :=
  {x | x normal = u normal + (if signs normal then s else -s) ∧
    ∀ i, i ≠ normal → DirectedInterval (u i) s (signs i) (x i)}

def inward (u : Vertex) : Fin 3 → Bool := fun i => decide (u i < 0)

def Prism (r : ℤ) : Set Vertex :=
  {x | -10*r ≤ x 0 ∧ x 0 ≤ 30*r+1 ∧
    ∀ i : Fin 3, i ≠ 0 → |x i| ≤ 10*r}

def axisCenter (a : ℤ) : Vertex := fun i => if i = 0 then a else 0

def forwardInward (u : Vertex) : Fin 3 → Bool :=
  fun i => if i = 0 then true else decide (u i < 0)

def contractionWidths (r R : ℤ) (t : ℕ) : Vertex :=
  fun h => if h.val < t then 2*r+(t : ℤ)*R else 4*r+(t : ℤ)*R

def HasInterface (r R : ℤ) (c w : Vertex) (T : Set Vertex) : Prop :=
  ∀ u ∈ Expand c w R, ∃ s : ℤ, s ∈ ({2*r,2*r+1,10*r} : Set ℤ) ∧
    Cube u s ⊆ Prism r ∧ ∃ h signs, QuarterFace u s h signs ⊆ T

def routeCenter (r : ℤ) (i : ℕ) : Vertex :=
  if i ≤ 3 then 0 else axisCenter (if i ≤ 12 then 2*r*(i-3 : ℕ) else 20*r+1)
def routeWidths (r R : ℤ) (i : ℕ) : Vertex :=
  if i ≤ 3 then contractionWidths r R i else fun _ => 2*r+(i : ℤ)*R

def P (r R : ℤ) (i : ℕ) : Set Vertex := Rect (routeCenter r i) (routeWidths r R i)

@[simp] theorem axisCenter_zero : axisCenter 0 = 0 := by ext i; simp [axisCenter]

def stepSize (r : ℤ) (i : ℕ) : ℤ := if i < 12 then 2*r else 2*r+1

@[simp] theorem P_zero (r R : ℤ) : P r R 0 = Cube 0 (4*r) := by
  simp only [P,routeCenter,routeWidths,Nat.zero_le,show 0 ≤ 3 by omega,ite_true,Cube]
  congr 1
  funext i
  simp [contractionWidths]

end LatticeRelay

end OAI


