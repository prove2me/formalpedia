-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
-- name    : OAI_Combinatorics_BinaryEdit_FiniteFourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:12:11.334316+00:00
-- url     : https://prove2.me/theorems/a7fc0929-dadd-4bea-bbd8-c2cbd3deae4e
-- title:
--   Normalized Fourier coefficients on a finite abelian group
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $A$ be a finite abelian group.
--
--   1. **Fourier coefficient.** For $f:A\to\mathbb C$ and a character $\chi$ of $A$,
--   $$
--   \hat f(\chi)=\frac1{|A|}\sum_{x\in A}\overline{\chi(x)}\,f(x),
--   $$
--   the inner product of $\chi$ with $f$ for the uniform probability weight. These are the scalar Fourier coefficients used in the finite-tree obstruction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteFourier.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteFourier.lean by skeleton subtraction
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

namespace OAI

/-!
# Fourier identities for the finite-tree obstruction

The scalar Fourier identities establish `lem:finite-fourier`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Finset RCLike

namespace TreeEdit.BinaryLower.FiniteFourier

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The normalized Fourier coefficient, with conjugation on the character. -/
def coefficient (f : A → ℂ) (χ : AddChar A ℂ) : ℂ :=
  RCLike.wInner RCLike.cWeight (χ : A → ℂ) f

end TreeEdit.BinaryLower.FiniteFourier

end

end OAI


