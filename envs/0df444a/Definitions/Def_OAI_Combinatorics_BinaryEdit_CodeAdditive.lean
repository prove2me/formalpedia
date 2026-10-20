-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
-- name    : OAI_Combinatorics_BinaryEdit_CodeAdditive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:53:20.274111+00:00
-- url     : https://prove2.me/theorems/82c35955-929c-49b9-9d7a-0d5fbecaaa95
-- title:
--   Encoded positions and unequal-label matches
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $c$ encode letters by binary blocks of length $P>0$, and let $x,y$ be words of length $M$.
--
--   1. **Original letter.** The encoded position $q<MP$ lies in block $\lfloor q/P\rfloor$, whose letter is $x_{\lfloor q/P\rfloor}$.
--   2. **Encoded bit.** The bit at position $q$ of $c(x)$; reading all positions recovers $c(x)$.
--   3. **Unequal edges.** For a matching $f,g$ of encoded positions, the matches $t$ whose original letters differ:
--   $$
--   x_{\lfloor f(t)/P\rfloor}\ne y_{\lfloor g(t)/P\rfloor}.
--   $$
--   Segment separation bounds the number of such matches.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CodeAdditive.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeAdditive.lean by skeleton subtraction
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

namespace OAI

/-! The longest encoded matching is partitioned by equality of its
original block labels. Segment separation and the span loss budget bound
the number of unequal-label matches. -/

namespace TreeEdit.BinaryLower.Code

universe u v

/-- The original letter whose block contains a specified encoded position. -/
def originalLetterAtBit {α : Type u} {M P : ℕ} (x : List α)
    (hx : x.length = M) (hP : 0 < P) (q : Fin (M*P)) : α :=
  x.get ⟨q.val/P, by rw [hx]; exact (Nat.div_lt_iff_lt_mul hP).mpr q.isLt⟩

/-- A bit of the actual concatenation, with its prescribed-length indexing. -/
def encodedBit {α : Type u} {β : Type v} {M P : ℕ}
    (c : α → Word β P) (x : List α) (hx : x.length = M)
    (q : Fin (M*P)) : β :=
  (encode c x).get ⟨q.val, by rw [length_encode, hx]; exact q.isLt⟩

/-- Reading all encoded positions reconstructs the concrete concatenation. -/
@[simp] theorem ofFn_encodedBit {α : Type u} {β : Type v} {M P : ℕ}
    (c : α → Word β P) (x : List α) (hx : x.length = M) :
    List.ofFn (encodedBit c x hx) = encode c x := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, length_encode, hx]
  · intro i hi hi'
    simp only [List.getElem_ofFn, encodedBit, List.get_eq_getElem]

/-- Precisely the selected unequal-original-label edges of a matching. -/
noncomputable def unequalEdges {α : Type u} {M P r : ℕ}
    (x y : List α) (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (f g : Fin r → Fin (M*P)) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun t =>
    originalLetterAtBit x hx hP (f t) ≠ originalLetterAtBit y hy hP (g t))

end TreeEdit.BinaryLower.Code

end OAI


