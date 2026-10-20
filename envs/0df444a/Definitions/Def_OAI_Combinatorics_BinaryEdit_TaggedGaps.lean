-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
-- name    : OAI_Combinatorics_BinaryEdit_TaggedGaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:47:27.894741+00:00
-- url     : https://prove2.me/theorems/4687c6c5-60af-4a4f-91b4-c7a54dd543bd
-- title:
--   Split transitions in block alignments
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Consider an alignment, given by increasing positions $u_0<\dots<u_n$ in one word and $v_0<\dots<v_n$ in another. Both words are cut into rows of $m$ blocks of width $B$, so a position $t$ lies in row $\lfloor t/B\rfloor/m$, rounded down.
--
--   1. **Split transitions.** Consecutive matches $i$ that stay in one source row but cross a target row boundary:
--   $$
--   \Bigl\lfloor\frac{u_i}{Bm}\Bigr\rfloor=\Bigl\lfloor\frac{u_{i+1}}{Bm}\Bigr\rfloor,\qquad\Bigl\lfloor\frac{v_i}{Bm}\Bigr\rfloor\ne\Bigl\lfloor\frac{v_{i+1}}{Bm}\Bigr\rfloor .
--   $$
--   2. **Split rows.** The source rows containing a split transition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean by skeleton subtraction
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

namespace OAI

/-! Gap accounting for split rows in ordered-tag alignments. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- Consecutive matching entries that cross a target-row boundary without
crossing a source-row boundary. -/
def splitTransitions {n : ℕ} (m B : ℕ) (u v : Fin (n + 1) → ℕ) :
    Finset (Fin n) :=
  univ.filter fun i => u i.castSucc / B / m = u i.succ / B / m ∧
    v i.castSucc / B / m ≠ v i.succ / B / m

/-- Source rows which contain such a transition. -/
def splitRows {n : ℕ} (m B : ℕ) (u v : Fin (n + 1) → ℕ) : Finset ℕ :=
  (splitTransitions m B u v).image fun i => u i.castSucc / B / m

end TreeEdit.BinaryLower.Tagged

end OAI


