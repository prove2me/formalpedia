-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
-- name    : OAI_Combinatorics_BinaryEdit_TaggedNonsplit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:49:32.987365+00:00
-- url     : https://prove2.me/theorems/3d903fbe-13b4-4eac-87e6-cf3ee10cc029
-- title:
--   Match counts per row
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words.
--
--   1. **Row count.** For an assignment $\mathrm{row}$ of $N$ matched pairs to row indices, the number of matches assigned to row $r$:
--   $$
--   n_r=\bigl|\{i<N:\ \mathrm{row}(i)=r\}\bigr| .
--   $$
--   These counts are used to charge the loss of a longest common subsequence to the source rows that are not split.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedNonsplit.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedNonsplit.lean by skeleton subtraction
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

namespace OAI

/-! Loss counting for nonsplit rows with a local row-pair matching bound. -/

namespace TreeEdit.BinaryLower.TaggedNonsplit

open scoped BigOperators

/-- Number of matches assigned to a natural row index. -/
def natRowCount {N : ℕ} (row : Fin N → ℕ) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun i => row i = r).card

end TreeEdit.BinaryLower.TaggedNonsplit

end OAI


