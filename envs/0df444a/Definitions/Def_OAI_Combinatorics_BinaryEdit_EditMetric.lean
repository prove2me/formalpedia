-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
-- name    : OAI_Combinatorics_BinaryEdit_EditMetric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:24:54.258345+00:00
-- url     : https://prove2.me/theorems/5e5a8847-d7ad-4f7b-b40b-e0bf832ff4a7
-- title:
--   Length bounds for edit scripts
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$.
--
--   1. **Length change.** One edit step changes the length by at most $1$, so a script of $n$ steps satisfies $|x|\le|y|+n$, and
--   $$
--   |x|\le|y|+\mathrm{ed}(x,y).
--   $$
--   2. **Empty word.** $\mathrm{ed}(x,\varnothing)=\mathrm{ed}(\varnothing,x)=|x|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/EditMetric.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/EditMetric.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion

namespace OAI

namespace TreeEdit.BinaryLower

universe u
variable {α : Type u}

namespace EditStep

theorem length_le {x y : List α} (h : EditStep x y) : x.length ≤ y.length + 1 := by
  cases h <;> simp only [List.length_append, List.length_cons] <;> omega

end EditStep

namespace EditScript

theorem length_le {x y : List α} {n : ℕ} (h : EditScript x y n) :
    x.length ≤ y.length + n := by
  induction h with
  | nil x => simp
  | cons hxy hyz ih => have := EditStep.length_le hxy; omega

end EditScript

theorem length_le_length_add_editDistance (x y : List α) : x.length ≤ y.length + ed x y :=
  EditScript.length_le (ed_script x y)

@[simp] theorem editDistance_nil_right (x : List α) : ed x [] = x.length := by
  apply Nat.le_antisymm
  · exact ed_le_of_script (EditScript.erase x)
  · simpa using length_le_length_add_editDistance x []

@[simp] theorem editDistance_nil_left (x : List α) : ed [] x = x.length := by
  rw [ed_comm, editDistance_nil_right]

namespace StrictEditScript

end StrictEditScript

end TreeEdit.BinaryLower

end OAI


