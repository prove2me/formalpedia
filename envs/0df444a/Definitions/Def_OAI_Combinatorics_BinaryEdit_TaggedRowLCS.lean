-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
-- name    : OAI_Combinatorics_BinaryEdit_TaggedRowLCS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:05:41.264211+00:00
-- url     : https://prove2.me/theorems/400f28e9-600c-4fe3-a0ee-5b4f6c0866d2
-- title:
--   Rows over block-indexed families
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words.
--
--   1. **Row.** For a family of words $X_1,\dots,X_m$ indexed by blocks, the concatenation
--   $$
--   \mathrm{row}(X)=X_1X_2\cdots X_m
--   $$
--   in increasing block order. When the blocks use pairwise disjoint alphabets, a common subsequence of two rows splits into common subsequences of corresponding blocks. This gives the LCS bounds for rows over tagged alphabets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedRowLCS.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedRowLCS.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Longest common subsequence bounds for rows over disjoint tagged alphabets. -/
namespace TreeEdit.BinaryLower.TaggedRow
open scoped BigOperators

/-- Concatenation in increasing block-index order. -/
def row {α : Type*} {m : ℕ} (blocks : Fin m → List α) : List α :=
  (List.finRange m).flatMap blocks

end TreeEdit.BinaryLower.TaggedRow

end OAI


