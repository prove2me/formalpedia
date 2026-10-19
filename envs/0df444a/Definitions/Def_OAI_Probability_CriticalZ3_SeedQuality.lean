-- Prove2me | Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
-- name    : OAI_Probability_CriticalZ3_SeedQuality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T18:14:53.218636+00:00
-- url     : https://prove2.me/theorems/8d7db099-821a-4c90-a026-f7329eb7e71a
-- title:
--   Seed events uniform in the percolation model
-- statement:
--   Seed-to-target events for bond and site percolation on $\mathbb Z^3$, written uniformly in the model.
--
--   1. **Basic adjacency.** In the bond model two vertices are adjacent through an open bond and every vertex counts as open. In the site model adjacency requires two neighbouring open vertices.
--   2. **Seed events.** For a centre $c$, radii $a\le b$ and a target set $T$, the seed event says that some open vertex $x$ of the cube $\Lambda_a(c)$ is joined to some $y\in T$ by an open path that stays inside $\Lambda_b(c)$:
--   $$
--   \exists x\in\Lambda_a(c),\ y\in T:\quad x\leftrightarrow y\ \text{inside }\Lambda_b(c).
--   $$
--   It agrees with the bond and site seed-reaching events defined earlier.
--   3. **Relay nodes.** For a wide enough box $C$ contained in a finite lattice graph, the relay centre of an exterior vertex is a vertex of that graph.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/SeedQuality.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/SeedQuality.lean by skeleton subtraction
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

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

def BasicAdj : (m : Model) → m.Config → Vertex → Vertex → Prop
  | .bond,ω => BondOpen ω
  | .site,ω => SiteOpen ω

def VertexOpen : (m : Model) → m.Config → Vertex → Prop
  | .bond,_,_ => True
  | .site,ω,x => ω x = true

def SeedReaches (m : Model) (c : Vertex) (a b : ℕ) (T : Set Vertex) : Set m.Config :=
  {ω | ∃ x ∈ cube c a, m.VertexOpen ω x ∧ ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c b) (m.BasicAdj ω)) x y}

@[simp] theorem seedReaches_bond (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    SeedReaches .bond c a b T = bondSeedReaches c a b T := by
  ext ω; simp [SeedReaches,bondSeedReaches,VertexOpen,BasicAdj]
@[simp] theorem seedReaches_site (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    SeedReaches .site c a b T = siteSeedReaches c a b T := rfl

end Model

namespace Box

end Box

namespace Model

end Model

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

noncomputable def relayNode (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox C) (y : Vertex) : G.Node :=
  ⟨C.relayCenter r y,G.containsBox_node hC
    (C.seedBox_contained r hw y _ (Box.center_mem_cube _ _))⟩

end LatticeGraph
end CriticalZ3

end OAI


