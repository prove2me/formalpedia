-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
-- name    : OAI_Combinatorics_BinaryEdit_Branching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:08:46.804356+00:00
-- url     : https://prove2.me/theorems/a2d7a5ac-1c4f-476e-be95-cec48743f5b7
-- title:
--   Active leaves and branching in ordered trees
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $\mathcal A$ be a predicate on nodes of a complete ordered tree, nodes being paths of child labels.
--
--   1. **Active children.** The number of children $v\,i$ of $v$ with $\mathcal A(v\,i)$.
--   2. **Active leaves.** The number of active descendants exactly $h$ levels below $v$.
--   3. **Branching condition.** $v$ branches at least $k$ to height $h$ if every active internal node of the subtree within height $h$ has at least $k$ active children. In that case an active $v$ has at least $k^h$ active descendants at depth $h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/Branching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Branching.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BinaryEditLower mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation

namespace OAI

/-!
# Counting active leaves in a full ordered tree

A node is its path, a list of child labels. `activeLeafCount A v h`
counts the active descendants exactly `h` edges below `v`. The condition
`BranchesAtLeast A k v h` concerns only internal nodes of that finite
subtree; it makes no assertion about children below its leaves.
-/

namespace TreeEdit.BinaryLower.Branching

variable {α : Type*} [Fintype α]

noncomputable def activeChildCount (A : List α → Prop) (v : List α) : ℕ :=
  by
    classical
    exact (Finset.univ.filter fun i => A (v ++ [i])).card

noncomputable def activeLeafCount (A : List α → Prop) (v : List α) : ℕ → ℕ
  | 0 => by
    classical
    exact if A v then 1 else 0
  | h + 1 => ∑ i : α, activeLeafCount A (v ++ [i]) h

def BranchesAtLeast (A : List α → Prop) (k : ℕ) (v : List α) : ℕ → Prop
  | 0 => True
  | h + 1 => (A v → k ≤ activeChildCount A v) ∧
      ∀ i : α, BranchesAtLeast A k (v ++ [i]) h

end TreeEdit.BinaryLower.Branching

end OAI


