-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
-- name    : OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:41:11.784661+00:00
-- url     : https://prove2.me/theorems/f0d473b3-f0e4-4a8e-9b6d-6a387b5243cc
-- title:
--   Matching events for codeword windows
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. A codebook assigns to each of $K$ labels a binary block of length $P$; windows are contiguous ranges of positions inside a block.
--
--   1. **Increasing positions.** Strictly increasing maps $\{1..s\}\to\{1..a\}$, equivalently $s$-element subsets of $\{1..a\}$.
--   2. **Segment matching event.** For labels $i,j$, window position maps $u,v$ of length $a$, and $s\in\mathbb N$, the set of codebooks $c$ for which some increasing $f,g$ satisfy
--   $$
--   c_i\bigl(u(f(t))\bigr)=c_j\bigl(v(g(t))\bigr)\quad(t\le s),
--   $$
--   i.e. the two windows have a common subsequence of length $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/SegmentMatchingCount.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SegmentMatchingCount.lean by skeleton subtraction
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

namespace OAI

namespace TreeEdit.BinaryLower.RandomMatching

/-- A choice of positions for a subsequence, in their original order. -/
abbrev IncreasingPositions (a s : ℕ) := {f : Fin s → Fin a // StrictMono f}

noncomputable def increasingPositionsEquiv (a s : ℕ) :
    IncreasingPositions a s ≃ {t : Finset (Fin a) // t.card = s} := by
  classical
  refine
    { toFun := fun f => ⟨Finset.univ.image f.1, by
        rw [Finset.card_image_of_injective _ f.2.injective]
        simp⟩
      invFun := fun t => ⟨t.1.orderEmbOfFin t.2, (t.1.orderEmbOfFin t.2).strictMono⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique (by
      rw [Finset.card_image_of_injective _ f.2.injective]
      simp) (fun x => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩) f.2).symm
  · intro t
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ t.1 t.2

/-- The event that two fixed windows admit a matching of size `s`. -/
noncomputable def segmentMatchingEvent {K P a : ℕ} (s : ℕ)
    (i j : Fin K) (u v : Fin a → Fin P) :
    Finset (Fin K → Fin P → Bool) := by
  classical
  exact Finset.univ.filter fun c =>
    ∃ f g : IncreasingPositions a s, ∀ t, c i (u (f.1 t)) = c j (v (g.1 t))

end TreeEdit.BinaryLower.RandomMatching

end OAI


