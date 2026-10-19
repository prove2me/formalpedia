-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Subunit
-- name    : OAI_Probability_CriticalZ3_Subunit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:42:43.120977+00:00
-- url     : https://prove2.me/theorems/f0cd9b21-edc8-484f-bee2-77587905476e
-- title:
--   Block percolation on the plane and the subunit parameter
-- statement:
--   A planar block percolation used to obtain a strict upper bound on the critical parameter.
--
--   1. **Active cells.** Each planar cell $v\in\mathbb Z^2$ has a finite set $J(v)$ of bits; $v$ is active if all of them are open, and bad otherwise. Two neighbouring cells are adjacent if both are active, and the planar cluster is the set of cells joined to $(0,0)$ by active paths, provided $(0,0)$ is active.
--   2. **Embedding.** The plane embeds into $\mathbb Z^3$ by $v\mapsto(v_1,v_2,0)$. The site block of $v$ is its image, and the bond block consists of the two bonds leaving it in directions $e_0,e_1$.
--   3. **Subunit parameter.** The parameter
--   $$
--   p_\ast=1-\frac{\varepsilon_0}4,\qquad\varepsilon_0=\tfrac12\cdot10^{-14},
--   $$
--   lies in $[0,1]$ and is used to show that percolation occurs below $p=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Subunit.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Subunit.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Definitions.Def_OAI_Probability_CriticalZ3_Exploration
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationInvariant
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationConnectivity
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationSurvival

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace BlockPercolation
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary
open Classical _root_.MeasureTheory ProbabilityTheory PlanarBoundary
variable {E : Type}

def active (J : Point → Finset E) (ω : E → Bool) (v : Point) : Prop :=
  ∀ e ∈ J v, ω e = true

def Bad (J : Point → Finset E) (v : Point) : Set (E → Bool) :=
  {ω | ¬active J ω v}

def Adj (J : Point → Finset E) (ω : E → Bool) (x y : Point) : Prop :=
  (∃ d : Direction, y = x+outward d) ∧ active J ω x ∧ active J ω y

def cluster (J : Point → Finset E) (ω : E → Bool) : Set Point :=
  {v | active J ω (0,0) ∧ Relation.ReflTransGen (Adj J ω) (0,0) v}

end BlockPercolation

namespace CriticalZ3
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary
open Classical _root_.MeasureTheory ProbabilityTheory PlanarBoundary

/-- The planar sublattice used only for the elementary strict upper threshold. -/
def planarEmbed (v : Point) : Vertex := ![v.1,v.2,0]

@[simp] theorem planarEmbed_zero : planarEmbed (0,0) = 0 := by
  funext i; fin_cases i <;> rfl

def planarSiteBlock (v : Point) : Finset Vertex := {planarEmbed v}

def planarBondBlock (v : Point) : Finset Bond := {(planarEmbed v,0),(planarEmbed v,1)}

noncomputable def subunitParameter : Set.Icc (0 : ℝ) 1 :=
  ⟨1-CriticalScales.contourError/4,by
    have hf0 := CriticalScales.contourError_pos
    have hf1 := CriticalScales.contourError_lt_half
    constructor <;> linarith⟩

end CriticalZ3

end OAI


