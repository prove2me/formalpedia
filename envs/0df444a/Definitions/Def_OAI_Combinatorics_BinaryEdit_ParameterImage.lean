-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
-- name    : OAI_Combinatorics_BinaryEdit_ParameterImage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:27:20.341129+00:00
-- url     : https://prove2.me/theorems/a163a8cc-489b-4db3-b54e-f822da5242ea
-- title:
--   Finite images of parameter spaces
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $A$ be a finite set and $G:A\to X$.
--
--   1. **Image.** The finite set $G(A)\subseteq X$.
--   2. **Map onto the image.** $a\mapsto G(a)$ as a map $A\to G(A)$, which may identify parameters with the same word.
--
--   Distortion lower bounds for the image are obtained by pulling embeddings of $G(A)$ back to $A$ and averaging over translations of the parameter group.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/ParameterImage.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/ParameterImage.lean by skeleton subtraction
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

namespace OAI

/-! Lower distortion bounds on the finite image of a parameter space. -/

noncomputable section
namespace TreeEdit.BinaryLower.ParameterImage

variable {A X : Type*} [Fintype A]

/-- The actual finite image of a finite parameter space. -/
def image (G : A → X) : Finset X := by
  classical
  exact Finset.univ.image G

lemma mem_image (G : A → X) (x : X) : x ∈ image G ↔ ∃ a, G a = x := by
  classical
  simp [image]

/-- The canonical map onto the finite image, allowing state-to-word collisions. -/
def toImage (G : A → X) (a : A) : {x : X // x ∈ image G} :=
  ⟨G a, (mem_image G (G a)).2 ⟨a, rfl⟩⟩

end TreeEdit.BinaryLower.ParameterImage

end

end OAI


