-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
-- name    : OAI_Analysis_Littlewood_SlotGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:15:24.764801+00:00
-- url     : https://prove2.me/theorems/969de563-9751-4a20-9939-3dbc55f430f6
-- title:
--   The slot hypergraph of a family of linear forms over a finite field and its slot densities
-- statement:
--   Let $I$ be a finite set of rows, $K$ a finite field, $V$ a finite $K$-vector space, $g_i:V\to K$ ($i\in I$) linear functionals, and $\mathrm{hit}\subseteq I\times K$ a decidable relation specifying the admissible values in each row. Write $\mathbf{1}[\cdot]$ for the indicator of a condition.
--
--   1. **Vertices.** $\mathcal{V}=\{(i,t)\in I\times K:\ \mathrm{hit}(i,t)\}$.
--
--   2. **Edges.** $\mathcal{E}=\{y\in V:\ \mathrm{hit}(i,g_i(y))\text{ for every }i\in I\}$.
--
--   3. **Support of an edge.** For $y\in V$, $\operatorname{supp}(y)=\{(i,g_i(y)):\ i\in I\}\subseteq I\times K$, so that $(i,t)\in\operatorname{supp}(y)$ if and only if $g_i(y)=t$.
--
--   4. **Slot density.** For $i\in I$ and $s\in K$,
--   $$
--   \rho(i,s)=\frac{1}{|\{y:\ g_i(y)=s\}|}\sum_{y\in V:\ g_i(y)=s}\ \prod_{j\in I,\ j\ne i}\mathbf{1}\bigl[\mathrm{hit}(j,g_j(y))\bigr],
--   $$
--   the proportion of points of the fiber $\{g_i=s\}$ whose values in all other rows are admissible (it is $0$ if the fiber is empty).
--
--   Each edge $y\in\mathcal{E}$ has exactly one vertex in every row, so $(\mathcal{V},\mathcal{E},\operatorname{supp})$ is an $|I|$-uniform hypergraph, and two edges $y,z$ have disjoint supports if and only if $g_i(y)\ne g_i(z)$ for every row $i$. If every $g_i$ is surjective, the degree of a vertex $(i,s)\in\mathcal{V}$ equals $\frac{|V|}{|K|}\rho(i,s)$; if in addition every pair $(g_i,g_j)$ with $i\ne j$ is surjective onto $K^2$, all codegrees are at most $|V|/|K|^2$. When the densities concentrate around a common value $p$, the almost perfect matching theorem of the Rödl nibble produces a large matching, i.e. many points $y$ all of whose values $g_i(y)$ are admissible and pairwise distinct within each row. With the random slot layouts modulo a prime this yields the points used in the signed interval packing.
--
--   **Formalization Note** `slotVertices hit`, `slotEdges g hit` and `slotSupport g y` are `Finset`s, with the simp lemma `mem_slotSupport`. `slotDensity g hit i s` is `avg` over the subtype `fiber (g i) s` of the product, over `j : {j : I // j ≠ i}`, of the indicators; `avg` divides by the cardinality, which gives $0$ on an empty fiber.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/SlotGraph.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/SlotGraph.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uK uV uJ

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset
open Nibble
section SlotGraph
variable {I : Type uI} {K : Type uK} {V : Type uV} [Fintype I] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

def slotVertices (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] : Finset (I × K) :=
  Finset.univ.filter (fun v ↦ hit v.1 v.2)

def slotEdges (g : I → V →ₗ[K] K) (hit : I → K → Prop) [∀ i t, Decidable (hit i t)] : Finset V :=
  Finset.univ.filter (fun y ↦ ∀ i, hit i (g i y))

def slotSupport (g : I → V →ₗ[K] K) (y : V) : Finset (I × K) :=
  Finset.univ.image (fun i ↦ (i,g i y))

omit [Fintype K] [Fintype V] [DecidableEq V] in
@[simp] lemma mem_slotSupport (g : I → V →ₗ[K] K) (y : V) (i : I) (t : K) :
    (i,t)∈slotSupport g y ↔ g i y=t := by
  simp [slotSupport,Prod.ext_iff]

def slotDensity (g : I → V →ₗ[K] K) (hit : I → K → Prop)
    [∀ i t, Decidable (hit i t)] (i : I) (s : K) : ℝ :=
  avg (fun y : fiber (g i) s ↦ ∏ j : {j : I // j≠i}, if hit j (g j y) then (1 : ℝ) else 0)

end SlotGraph
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
section RandomMatching
variable {I : Type} [Fintype I] [DecidableEq I]

end RandomMatching
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble
attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI


