-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
-- name    : OAI_Combinatorics_BinaryEdit_Distortion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:23:05.413712+00:00
-- url     : https://prove2.me/theorems/507907b7-ec72-4847-a54b-680816129204
-- title:
--   Expansion and contraction ratios of embeddings into l1
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $(X,\rho)$ be a finite set with a distance function and $f:X\to\ell_1$.
--
--   1. **Expansion and contraction ratios.** The sets
--   $$
--   \Bigl\{\frac{\|f(x)-f(y)\|_1}{\rho(x,y)}\Bigr\}_{x\ne y},\qquad\Bigl\{\frac{\rho(x,y)}{\|f(x)-f(y)\|_1}\Bigr\}_{x\ne y}.
--   $$
--   2. **Distortions.** The distortion of $f$ is the product of the suprema of these two sets. The set of distortions of injective maps has infimum $c_1(X,\rho)$, the $\ell_1$-distortion of $X$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/Distortion.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Distortion.lean by skeleton subtraction
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

namespace OAI

/-! Distortion of finite metric spaces under injective maps into real ℓ₁. -/

noncomputable section
open scoped ENNReal

namespace TreeEdit.BinaryLower

variable {X Y : Type*}

/-- The two finite sets whose maxima define distortion. -/
def expansionRatios (ρ : X → X → ℝ) (f : X → RealL1) : Set ℝ :=
  {r | ∃ x y, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y}

def contractionRatios (ρ : X → X → ℝ) (f : X → RealL1) : Set ℝ :=
  {r | ∃ x y, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}

def embeddingDistortions (ρ : X → X → ℝ) : Set ℝ :=
  {D | ∃ f : X → RealL1, Function.Injective f ∧ D = distortion ρ f}

end TreeEdit.BinaryLower

end

end OAI


