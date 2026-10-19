-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
-- name    : OAI_Probability_CriticalZ3_RelayProbability
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:20:30.892508+00:00
-- url     : https://prove2.me/theorems/5c78764c-c4cc-4b37-856b-a546c2e35c30
-- title:
--   Route boxes and uniform parameters inside a region
-- statement:
--   Notation for transporting the relay route by symmetries and controlling parameters on it.
--
--   1. **Internal bits.** A bond is internal to a set $D$ of vertices if both endpoints lie in $D$; a site is internal if it lies in $D$. A parameter field $p$ is uniform with value $q$ on $D$ if $p_e=q$ for every internal bit $e$.
--   2. **Containment.** A finite lattice graph contains a set $D$ if it contains all vertices of $D$ and all bonds between them.
--   3. **Boxes.** For a centre $c$ and nonnegative widths $w$, the box is $[c-w,c+w]$. Its image under a signed symmetry $S$ (with permutation $\pi$) is the box
--   $$
--   [S(c)-w\circ\pi,\ S(c)+w\circ\pi].
--   $$
--   The $i$-th route box is the image under $S$ of the $i$-th relay rectangle, for scale data with parameters $r,R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/RelayProbability.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/RelayProbability.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_CriticalZ3_Relay

namespace OAI

universe uOmega

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Model

def Internal : (m : Model) → Set Vertex → m.Bit → Prop
  | .bond,D,e => e.1 ∈ D ∧ step e.1 e.2 ∈ D
  | .site,D,x => x ∈ D

def UniformOn (m : Model) (p : m.Bit → Set.Icc (0:ℝ) 1)
    (q : Set.Icc (0:ℝ) 1) (D : Set Vertex) : Prop := ∀ e, m.Internal D e → p e = q

end Model

namespace LatticeGraph
variable (G : LatticeGraph)
def ContainsSet (D : Set Vertex) : Prop :=
  (∀ x ∈ D, x ∈ G.vertices) ∧ ∀ e : Bond, e.1 ∈ D → step e.1 e.2 ∈ D → e ∈ G.edges

end LatticeGraph

namespace Box

def rect (c w : Vertex) (hw : ∀ i, 0 ≤ w i) : Box :=
  ⟨fun i => c i-w i,fun i => c i+w i,fun i => by linarith [hw i]⟩

def framedRect (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i) : Box :=
  rect (S.vertex c) (fun i => w (S.perm i)) (fun i => hw (S.perm i))

end Box

namespace ScaleData
variable {model : Model} (s : ScaleData model)

end ScaleData
end CriticalZ3

namespace MeasureTheory
open scoped _root_.MeasureTheory
open Classical
variable {Ω : Type uOmega} [MeasurableSpace Ω]
end MeasureTheory

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem route_width_nonneg (i : ℕ) (j : Fin 3) : 0 ≤ LatticeRelay.routeWidths s.r s.R i j := by
  unfold LatticeRelay.routeWidths
  split_ifs
  · dsimp [LatticeRelay.contractionWidths]
    split_ifs <;> positivity
  · positivity

def routeBox (S : SignedSymmetry) (i : ℕ) : Box :=
  Box.framedRect S (LatticeRelay.routeCenter s.r i) (LatticeRelay.routeWidths s.r s.R i)
    (s.route_width_nonneg i)

end ScaleData
end CriticalZ3

end OAI


