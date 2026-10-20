-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
-- name    : OAI_Combinatorics_BinaryEdit_EncodedImage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:32:02.133054+00:00
-- url     : https://prove2.me/theorems/8acaada6-7d8b-4ba5-9287-c8705486c872
-- title:
--   Encoded words and their finite image
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $c$ assign to each letter of $\alpha$ a binary word of length $P$.
--
--   1. **Encoded word.** For $x$ of length $M$, its encoding $c(x)$ as a binary word of length $MP$.
--   2. **Encoded set.** For a finite set $W$ of words, the image
--   $$
--   c(W)=\{c(x):\ x\in W\},
--   $$
--   and the map $x\mapsto c(x)$ from $W$ to $c(W)$. Distortion lower bounds transfer from $W$ to $c(W)$ when $c$ distorts edit distance boundedly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/EncodedImage.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/EncodedImage.lean by skeleton subtraction
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

namespace OAI

/-! Distortion transport through finite images of fixed-width codes. -/

noncomputable section
namespace TreeEdit.BinaryLower

universe u

/-- The concatenation extension, viewed in its exact-length target type. -/
def encodedWord {α : Type u} {M P : ℕ} (c : α → Word Bool P)
    (x : Word α M) : Word Bool (M * P) :=
  ⟨encode c x.val, by rw [length_encode, x.property]⟩

/-- The actual finite image, rather than an abstract copy of the source set. -/
def encodedSet {α : Type u} {M P : ℕ} (c : α → Word Bool P)
    (W : Finset (Word α M)) : Finset (Word Bool (M * P)) :=
  W.image (encodedWord c)

/-- The map from source membership witnesses into membership witnesses of the
encoded finite set, with no choice of an inverse. -/
def encodedMember {α : Type u} {M P : ℕ} (c : α → Word Bool P)
    (W : Finset (Word α M)) : {x : Word α M // x ∈ W} →
      {y : Word Bool (M * P) // y ∈ encodedSet c W} :=
  fun x => ⟨encodedWord c x.val, Finset.mem_image_of_mem _ x.property⟩

end TreeEdit.BinaryLower

end

end OAI


