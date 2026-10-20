-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
-- name    : OAI_Combinatorics_BinaryEdit_RandomMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:40:14.651718+00:00
-- url     : https://prove2.me/theorems/d36229f8-7f38-4078-8c63-70d63600ff6b
-- title:
--   Counting functions satisfying matching constraints
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $A,B$ be finite sets, $\ell:I\to A$ and $r:I\to A$ with $r$ injective and $\ell(i)\ne r(j)$ for all $i,j$.
--
--   1. **Constraint equivalence.** The functions $f:A\to B$ with
--   $$
--   f(\ell(i))=f(r(i))\quad\text{for all }i
--   $$
--   correspond bijectively to arbitrary functions on $A\setminus r(I)$: the values at the targets $r(i)$ are forced. Hence a uniformly random $f$ satisfies all constraints with probability $|B|^{-|I|}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/RandomMatching.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/RandomMatching.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

/-!
Exact finite counting for the prescribed-match probability in
`polynomial-code.tex`, Lemma `lem:random-segments`.
The constraints identify distinct target coordinates with coordinates outside
that target set.
-/

namespace TreeEdit.BinaryLower.RandomMatching

open Function

variable {A I B : Type*}

/-- The coordinates outside the prescribed right endpoints are free. -/
noncomputable def constraintEquiv
    (l : I → A) (r : I ↪ A) (hdisj : ∀ i j, l i ≠ r j) :
    {f : A → B // ∀ i, f (l i) = f (r i)} ≃
      ({a : A // a ∉ Set.range r} → B) := by
  classical
  let extend (g : {a : A // a ∉ Set.range r} → B) (a : A) : B :=
    if h : a ∈ Set.range r then
      g ⟨l (Classical.choose h), by
        rintro ⟨j, hj⟩
        exact hdisj (Classical.choose h) j hj.symm⟩
    else g ⟨a, h⟩
  have hl (g : {a : A // a ∉ Set.range r} → B) (i : I) :
      extend g (l i) = g ⟨l i, by
        rintro ⟨j, hj⟩
        exact hdisj i j hj.symm⟩ := by
    simp only [extend]
    split_ifs with h
    · obtain ⟨j, hj⟩ := h
      exact False.elim (hdisj i j hj.symm)
    · rfl
  have hr (g : {a : A // a ∉ Set.range r} → B) (i : I) :
      extend g (r i) = g ⟨l i, by
        rintro ⟨j, hj⟩
        exact hdisj i j hj.symm⟩ := by
    simp only [extend]
    split_ifs with h
    · have heq : Classical.choose h = i := r.injective (Classical.choose_spec h)
      exact congrArg g (Subtype.ext (congrArg l heq))
    · exact False.elim (h ⟨i, rfl⟩)
  refine
    { toFun := fun f a => f.1 a.1
      invFun := fun g => ⟨extend g, fun i => (hl g i).trans (hr g i).symm⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Subtype.ext
    funext a
    dsimp only
    simp only [extend]
    split_ifs with h
    · exact (f.2 (Classical.choose h)).trans
        (congrArg f.1 (Classical.choose_spec h))
    · rfl
  · intro g
    funext a
    simp only [extend, dite_eq_right a.2]

end TreeEdit.BinaryLower.RandomMatching

end OAI


