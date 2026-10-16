-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
-- name    : OAI_Combinatorics_TreeEdit_TreeArithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:19:15.261613+00:00
-- url     : https://prove2.me/theorems/d779dd72-c76d-4d21-9065-e5b0ca20d933
-- title:
--   Word length at height $h$ of a tree construction
-- statement:
--   For natural numbers $m$ and $T$, the length function $\ell_{m,T}:\mathbb{N}\to\mathbb{N}$ is defined recursively by
--
--   $$\ell_{m,T}(0)=1,\qquad \ell_{m,T}(h+1)=T\cdot\bigl(m\cdot\ell_{m,T}(h)\bigr)\quad(h\ge 0),$$
--
--   so that $\ell_{m,T}(h)=(mT)^h$.
--
--   In a tree construction of words over a complete $m$-ary tree, a leaf carries a single symbol and an internal node carries $T$ rows, each row the concatenation of the words of its $m$ children. A node of height $h$ therefore carries a word of length $\ell_{m,T}(h)$; with the root at height $k$, the constructed words have length $(mT)^k$.
--
--   **Formalization Note** The Lean name is `FiniteTree.length m T h`, declared reducible. The order of the factors, $T\cdot(m\cdot\ell)$, matches the length `T * (m * B)` of the cyclic interleaving of fixed-length words.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/TreeArithmetic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/TreeArithmetic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords

namespace OAI

namespace TreeEdit.FiniteTree

universe u

attribute [local instance] Classical.propDecidable

@[reducible] def length (m T : ℕ) : ℕ → ℕ
  | 0 => 1
  | h + 1 => T * (m * length m T h)

end TreeEdit.FiniteTree

end OAI


