-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_BlockEmbedding
-- name    : OAI_Probability_ThorpShuffle_BlockEmbedding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T04:23:14.728626+00:00
-- url     : https://prove2.me/theorems/d7549730-5d58-4e3b-a4db-f670a05ad19f
-- title:
--   The points outside one block of a product $I\times\beta$
-- statement:
--   Let $I$ be a set of *blocks* and $\beta$ a set of *positions within a block*, so that $I\times\beta$ is a disjoint union of the blocks $\{j\}\times\beta$. For a block $i\in I$, the complement of block $i$ is
--   $$\operatorname{Comp}(i)=\{j\in I: j\ne i\}\times\beta,$$
--   the set of points $(j,b)$ of $I\times\beta$ that do not lie in block $i$. When $I$ and $\beta$ are finite, $\operatorname{Comp}(i)$ is a finite set with $(|I|-1)\,|\beta|$ elements.
--
--   This set is used in the block setting where a finite set $\alpha$ is identified with $I\times\beta$ through a bijection $e:\alpha\to I\times\beta$ and a family of permutations $(p_j)_{j\in I}$ of $\beta$ acts on $\alpha$ blockwise (point $e^{-1}(j,b)$ goes to $e^{-1}(j,p_j(b))$). For the subgroup $B_i$ of permutations that move only the points of block $i$, a left coset $gB_i$ of a permutation $g$ of $\alpha$ is determined by the restriction of $g$ to the points $e^{-1}(\operatorname{Comp}(i))$ outside block $i$; $\operatorname{Comp}(i)$ is the index set of that restriction, which is how coset masses $\nu(gB_i)$ are organised.
--
--   **Formalization Note** The Lean definition is `complement i := {j : I // j ≠ i} × β` in the namespace `OAI.Thorp.Block`, together with its `Fintype` instance (the unnamed member of the bundle). The blockwise embedding itself (`Block.perm`, `Block.hom`, `Block.embedding`) belongs to the main definitions of this development.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/BlockEmbedding.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/BlockEmbedding.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment
import Definitions.Def_OAI_Probability_ThorpShuffle_Reynolds
import Definitions.Def_OAI_Probability_ThorpShuffle_FourierFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_JointProjectors
import Definitions.Def_OAI_Probability_ThorpShuffle_ProductProjectors
import Definitions.Def_OAI_Probability_ThorpShuffle_SymmetricFamilies

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uβ uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Block
open scoped Classical
variable {I : Type uI} {β : Type uβ} {α : Type uα}

def complement (i : I) := {j : I // j ≠ i} × β

instance [Fintype I] [Fintype β] (i : I) : Fintype (complement (β:=β) i) :=
  inferInstanceAs (Fintype ({j : I // j ≠ i} × β))

end Thorp.Block

end

end OAI


