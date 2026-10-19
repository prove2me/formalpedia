-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
-- name    : OAI_Analysis_Littlewood_DependentMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:13:19.53736+00:00
-- url     : https://prove2.me/theorems/86f3bf8f-c05c-4771-9350-c0b02349990b
-- title:
--   Good points for a family of linear forms relative to a target set and a forbidden set
-- statement:
--   Let $K$ be a finite field, $V$ a finite $K$-vector space, $J$ a finite index set and $g_j:V\to K$ ($j\in J$) linear functionals. Given finite sets $G,S\subseteq K$, a point $y\in V$ is called **good** if
--   $$
--   g_j(y)\in G\ \text{ for all } j\in J,\qquad g_j(y)+g_l(y)\notin S\ \text{ and }\ g_j(y)-g_l(y)\notin S\ \text{ for all } j\ne l .
--   $$
--
--   In the averaged variance estimate for the slot hypergraph, $K=\mathbb{Z}/q\mathbb{Z}$, $G$ is the catalogue of interior signed sites and $S$ is a short neighbourhood of $0$. Two catalogue elements from the same chunk always have sum or difference in $S$, so at a good point the values $g_j(y)$ lie in pairwise different chunks, and the events that they are hit, under independent random choices per chunk, are independent. Bad points are rare: if every $g_j$ and every pair $(g_j,g_l)$ with $j\ne l$ is surjective, the proportion of bad points is at most $|J|(|K|-|G|)/|K|+2|J|^2|S|/|K|$, which feeds the variance bound.
--
--   **Formalization Note** `rowsGood g G S y` is a `Prop`, and `rowsGoodDecidable` is a local instance deciding it classically. The remaining sections of the file only declare variables.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/DependentMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/DependentMoments.lean by skeleton subtraction
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

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uκ uA uJ uY uV uK uΩ uI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section ProductMoments
variable {κ : Type uκ} {A : Type uA} {J : Type uJ} {Y : Type uY} [Fintype κ] [DecidableEq κ] [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype J] [Fintype Y] [Nonempty Y]

end ProductMoments
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section ConditionalAverage
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

end ConditionalAverage
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section GoodRows
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

def rowsGood (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) : Prop :=
  (∀ j, g j y∈G) ∧ ∀ j l, j≠l → g j y+g l y∉S ∧ g j y-g l y∉S

noncomputable local instance rowsGoodDecidable (g : J → V →ₗ[K] K) (G S : Finset K) (y : V) :
    Decidable (rowsGood g G S y) := Classical.propDecidable _

end GoodRows
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section AveragedVariance
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} {A : Type uA} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Nonempty A] [DecidableEq A]

end AveragedVariance
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI


