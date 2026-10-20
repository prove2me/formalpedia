-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
-- name    : OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:54:38.786788+00:00
-- url     : https://prove2.me/theorems/54912376-b27c-4e23-907a-56dabfffacfd
-- title:
--   Spans of matching labels
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $f:\{1..r\}\to\{1..n\}$ be a matching of positions and $\mathrm{label}:\{1..r\}\to\beta$.
--
--   1. **Matching span.** For a label $b$, the integer interval hull of the positions carrying label $b$:
--   $$
--   \mathrm{span}(b)=\{t:\ f(i)\le t\le f(j)\text{ for some }i,j\text{ with }\mathrm{label}(i)=\mathrm{label}(j)=b\},
--   $$
--   empty if no match has label $b$. Disjointness of spans for an increasing matching yields a budget on the total loss.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/MatchingSpanBudget.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/MatchingSpanBudget.lean by skeleton subtraction
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

namespace OAI

namespace TreeEdit.BinaryLower

noncomputable section

/-- The integer interval hull of the positions bearing one matching label.
The empty fiber has empty span. -/
def matchingSpan {r n : ℕ} {β : Type*} [DecidableEq β] (f : Fin r → Fin n)
    (label : Fin r → β) (b : β) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ i j, label i = b ∧ label j = b ∧ f i ≤ p ∧ p ≤ f j

@[simp] theorem mem_matchingSpan {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (label : Fin r → β) (b : β) (p : Fin n) :
    p ∈ matchingSpan f label b ↔
      ∃ i j, label i = b ∧ label j = b ∧ f i ≤ p ∧ p ≤ f j := by
  classical
  simp [matchingSpan]

end
end TreeEdit.BinaryLower

end OAI


