-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_UnequalSegments
-- name    : OAI_Combinatorics_BinaryEdit_UnequalSegments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:57:52.112988+00:00
-- url     : https://prove2.me/theorems/25b9aebd-bd64-4eba-99f3-2d8605f0d0cf
-- title:
--   Segment separation for selected block pairs
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $x,y$ be words of length $MP$, viewed as $M$ blocks of width $P$, let $\mathrm{bad}$ be a relation on block pairs and $a_0\in\mathbb N$.
--
--   1. **Block segment separation.** For every bad pair of blocks $(b_1,b_2)$ and windows of equal length $a\ge a_0$ inside block $b_1$ of $x$ and block $b_2$ of $y$, every common subsequence $w$ of the two windows satisfies
--   $$
--   100\,|w|\le99\,a .
--   $$
--   For an encoding by a segment-separated codebook this holds for all pairs of blocks with unequal letters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/UnequalSegments.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/UnequalSegments.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments

namespace OAI

namespace TreeEdit.BinaryLower.Code

/-- Concrete separation of segments in a selected pair of width-`P` blocks.
The words here are indexed functions solely to avoid casts in total length. -/
def BlockSegmentSeparation {α : Type*} {M P : ℕ}
    (x y : Fin (M * P) → α) (bad : ℕ × ℕ → Prop) (a₀ : ℕ) : Prop :=
  ∀ b : ℕ × ℕ, bad b → b.1 < M → b.2 < M →
    ∀ i j a : ℕ, b.1 * P ≤ i → i + a ≤ (b.1 + 1) * P →
      b.2 * P ≤ j → j + a ≤ (b.2 + 1) * P → a₀ ≤ a →
      ∀ w : List α,
        w.Sublist (((List.ofFn x).drop i).take a) →
        w.Sublist (((List.ofFn y).drop j).take a) →
        100 * w.length ≤ 99 * a

end TreeEdit.BinaryLower.Code

end OAI


