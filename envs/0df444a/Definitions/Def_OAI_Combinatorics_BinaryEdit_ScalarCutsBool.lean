-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
-- name    : OAI_Combinatorics_BinaryEdit_ScalarCutsBool
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:15:36.898644+00:00
-- url     : https://prove2.me/theorems/b8ac1c53-ea33-4ae8-9a7a-693aa9e0afa7
-- title:
--   Cut distances and zero-one steps
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words.
--
--   1. **Bit and cut distance.** For $b\in\{0,1\}$ its real value, and for a cut $C:S\to\{0,1\}$ of a set $S$,
--   $$
--   d_C(x,y)=|C(x)-C(y)| ,
--   $$
--   the cut pseudometric.
--   2. **Steps.** $\sigma_k(i)=\mathbf 1[k<i]$, a zero-one threshold function on $\mathbb N$.
--
--   For a nondecreasing sequence $g$, $|g_i-g_j|=\sum_k(g_{k+1}-g_k)\,|\sigma_k(i)-\sigma_k(j)|$; sorting the values of one real coordinate thus writes its distances as a nonnegative combination of cut distances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/ScalarCutsBool.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/ScalarCutsBool.lean by skeleton subtraction
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

namespace OAI

/-! Scalar finite cut decomposition used by the finite-group obstruction.
This is the one-real-coordinate part of `lem:cuts` in preliminaries.tex. -/

namespace TreeEdit.BinaryLower.BoolCuts

open scoped BigOperators

noncomputable def bit (b : Bool) : ℝ := if b then 1 else 0

noncomputable def cutDistance {S : Type*} (C : S → Bool) (x y : S) : ℝ :=
  |bit (C x) - bit (C y)|

/-- A threshold viewed as a real-valued zero-one step. -/
noncomputable def step (k i : ℕ) : ℝ := if k < i then 1 else 0

end TreeEdit.BinaryLower.BoolCuts

end OAI


