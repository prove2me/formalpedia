-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
-- name    : OAI_Combinatorics_BinaryEdit_SegmentCode
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:51:20.717979+00:00
-- url     : https://prove2.me/theorems/0b9b58d9-b442-4b0c-93c0-7e72ea67ce1f
-- title:
--   Segment-separated binary codebooks
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. A codebook assigns to each of $K$ labels a binary block of length $P$; windows are contiguous ranges of positions inside a block. Let $c$ be a binary codebook with $K$ labels and block length $P$.
--
--   1. **Window.** The positions $i,i+1,\dots,i+a-1$ of a block, when $i+a\le P$.
--   2. **Segment separation.** $c$ is segment-separated beyond $a_0$ if for distinct labels $k\ne l$, every $a\ge a_0$ and all windows of length $a$ in $c_k$ and $c_l$, every common subsequence of length $s$ of the two windows satisfies
--   $$
--   100\,s\le99\,a .
--   $$
--   3. **Bad comparisons.** For one comparison, the codebooks whose windows share a common subsequence of length $a-\lfloor a/100\rfloor$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SegmentCode.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SegmentCode.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite probabilistic construction of a codebook simultaneously separating every
long segment of every pair of differently labelled blocks. Counting is done on
all Boolean codebooks, so no randomness or existence hypothesis is retained.
-/

namespace TreeEdit.BinaryLower.SegmentCode

open RandomMatching CodeUnionBound

/-- A contiguous window of positions in a block. -/
def window {P : ℕ} (a i : ℕ) (h : i+a ≤ P) : Fin a → Fin P :=
  fun t => ⟨i+t.val, by have := t.isLt; omega⟩

/-- Segment separation in terms of increasing position lists. -/
def SegmentSeparated {K P : ℕ} (c : Fin K → Fin P → Bool) (a₀ : ℕ) : Prop :=
  ∀ (k l : Fin K), k ≠ l → ∀ (a i j : ℕ), a₀ ≤ a →
    ∀ (hi : i+a ≤ P) (hj : j+a ≤ P) (s : ℕ)
      (f g : IncreasingPositions a s),
      (∀ t, c k (window a i hi (f.1 t)) = c l (window a j hj (g.1 t))) →
        100*s ≤ 99*a

/-- Bad comparisons include only valid windows longer than the cutoff. -/
noncomputable def comparisonBad {K P : ℕ} (a₀ : ℕ)
    (t : SegmentComparison K (P+1)) : Finset (Fin K → Fin P → Bool) := by
  classical
  rcases t with ⟨k, l, a, i, j⟩
  exact if h : k ≠ l ∧ a₀ ≤ a.val ∧ i.val+a.val ≤ P ∧ j.val+a.val ≤ P then
    segmentMatchingEvent (a.val-a.val/100) k l
      (window a.val i.val h.2.2.1) (window a.val j.val h.2.2.2)
  else ∅

end TreeEdit.BinaryLower.SegmentCode

end OAI


