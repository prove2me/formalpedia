-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
-- name    : OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:09:32.588822+00:00
-- url     : https://prove2.me/theorems/86e00d6a-ce02-408e-8d01-547793f7a6d2
-- title:
--   Sparse active nodes for characters
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $G$ be a finite abelian group and $w$ assign an element of $G$ to each node of a complete tree of depth $h$ over an alphabet $\alpha$.
--
--   1. **Internal nodes.** Pairs (depth $j<h$, a path of length $j$).
--   2. **Sparse node.** An active node with fewer than $b$ active children.
--   3. **Character sparsity.** For a character $\chi$ of $G$, the node $v$ is active if
--   $$
--   \chi\bigl(w(v)\bigr)\ne1 ,
--   $$
--   and $v$ is character-sparse if it is sparse for this activity. Without sparse active nodes the active leaves are numerous, which controls the Fourier mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteActivityBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteActivityBridge.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching

namespace OAI

/-!
# Finite indices for the sparse-activity obstruction

Internal nodes are indexed by their depth and finite sequence of child
indices. Absence of a sparse active node bounds the cardinality of active
leaves, which controls the Fourier mass.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical

/-- All internal nodes of a complete tree of depth `h`. -/
abbrev InternalNode (α : Type*) (h : ℕ) := Σ j : Fin h, Fin (j : ℕ) → α

/-- A bad node is active but has fewer than `b` active children. -/
def sparseNode {α : Type*} [Fintype α] {h : ℕ}
    (active : List α → Prop) (b : ℕ) (v : InternalNode α h) : Prop :=
  active (List.ofFn v.2) ∧
    Branching.activeChildCount active (List.ofFn v.2) < b

/-- Character formulation of the sparse-node predicate. -/
def characterSparse {α G : Type*} [Fintype α] [AddCommGroup G] {h : ℕ}
    (w : List α → G) (b : ℕ) (v : InternalNode α h) (χ : AddChar G ℂ) : Prop :=
  sparseNode (fun p => χ (w p) ≠ 1) b v

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI


