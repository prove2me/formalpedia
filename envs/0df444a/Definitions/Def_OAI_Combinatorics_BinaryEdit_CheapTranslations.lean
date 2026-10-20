-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
-- name    : OAI_Combinatorics_BinaryEdit_CheapTranslations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:22:23.302991+00:00
-- url     : https://prove2.me/theorems/990f462c-2911-4f7d-9c0f-7d9132d92294
-- title:
--   Row windows and orbit rows
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $\mathrm{row}$ assign a word to each index or each element of an additive monoid $A$.
--
--   1. **Row window.** The concatenation of the rows $\mathrm{row}(s),\mathrm{row}(s+1),\dots,\mathrm{row}(s+c-1)$.
--   2. **Orbit rows.** For $x,u\in A$ and $T\in\mathbb N$,
--   $$
--   \mathrm{row}(x)\,\mathrm{row}(x+u)\cdots\mathrm{row}\bigl(x+(T-1)u\bigr),
--   $$
--   the word produced by repeated translation by $u$. Shifting $x$ by $u$ deletes the first row and appends one row, so it costs few edits.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CheapTranslations.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CheapTranslations.lean by skeleton subtraction
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

namespace OAI

/-!
# Inexpensive translations

Elementary unrestricted edit scripts give the translation estimates in
`lem:finite-cost`.
-/

namespace TreeEdit.BinaryLower.CheapTranslations

universe u v

variable {α : Type u}

/-- A consecutive finite window of rows, concatenated in increasing order. -/
def rowWindow (rows : ℕ → List α) (start count : ℕ) : List α :=
  (List.range' start count).flatMap rows

/-- The row word arising from repeated translation in an additive parameter
space. This is the row operation in both tree constructions. -/
def orbitRows {A : Type v} [AddMonoid A] (row : A → List α)
    (x u : A) (T : ℕ) : List α :=
  rowWindow (fun j => row (x + j • u)) 0 T

end TreeEdit.BinaryLower.CheapTranslations

end OAI


