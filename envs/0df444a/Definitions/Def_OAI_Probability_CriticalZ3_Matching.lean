-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_Matching
-- name    : OAI_Probability_CriticalZ3_Matching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:26:06.469982+00:00
-- url     : https://prove2.me/theorems/1ed719ec-21bc-4a90-bd1e-04c70f2f2e89
-- title:
--   Incidence and conflict for edges, and valid boundary codes
-- statement:
--   Finite combinatorics for the contour estimate.
--
--   1. **Incidence and conflict.** For edges $e$ with endpoints $a(e),b(e)$, the edges incident to $v$ are those with an endpoint $v$, and two edges conflict if they share an endpoint:
--   $$
--   \{a(e),b(e)\}\cap\{a(f),b(f)\}\ne\varnothing .
--   $$
--   Choosing one endpoint of each edge of a matching gives distinct vertices.
--   2. **Primal cells.** Each boundary side of a set $X$ of planar cells has an inside cell in $X$ and an outside cell, its outward neighbour.
--   3. **Valid codes.** A code is valid if its traced sides are distinct boundary sides of some finite set $X$. The inner and outer cells of the $i$-th traced side are then defined.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Matching.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Matching.lean by skeleton subtraction
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

namespace OAI

universe uAlpha uE uV

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Exact greedy constants used in the shell trials and contour estimate. -/
namespace GreedyPacking
open Classical

variable {α : Type uAlpha}

end GreedyPacking

namespace FiniteMatching
open Classical
variable {E : Type uE} {V : Type uV} [Fintype E]

noncomputable def incident (a b : E → V) (v : V) : Finset E :=
  Finset.univ.filter (fun e => a e = v ∨ b e = v)

def conflict (a b : E → V) (e f : E) : Prop :=
  a e = a f ∨ a e = b f ∨ b e = a f ∨ b e = b f

/- Choosing either endpoint of each edge of a matching gives distinct vertices. -/
end FiniteMatching

namespace PlanarBoundary
open Classical

def primalInside {X : Finset Point} (e : Boundary X) : Point := e.val.1
def primalOutside {X : Finset Point} (e : Boundary X) : Point := e.val.1+outward e.val.2

def Valid {n : ℕ} (c : Code n) : Prop :=
  ∃ X : Finset Point, ∃ e : Fin n → Boundary X, Function.Injective e ∧
    ∀ i, traceSide c i = (e i).val

def inner {n : ℕ} (c : Code n) (i : Fin n) : Point := (traceSide c i).1
def outer {n : ℕ} (c : Code n) (i : Fin n) : Point :=
  (traceSide c i).1+outward (traceSide c i).2

end PlanarBoundary

end OAI


