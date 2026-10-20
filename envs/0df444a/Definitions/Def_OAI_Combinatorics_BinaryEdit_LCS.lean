-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
-- name    : OAI_Combinatorics_BinaryEdit_LCS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:57:33.821785+00:00
-- url     : https://prove2.me/theorems/456d1233-1a34-461b-b34e-a1b647099f0f
-- title:
--   Basic properties of the longest common subsequence
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$.
--
--   1. **Empty words.** $\mathrm{lcs}(\varnothing,x)=\mathrm{lcs}(x,\varnothing)=0$.
--   2. **Equality.** For words of equal length,
--   $$
--   \mathrm{lcs}(x,y)=|x|\iff x=y ,
--   $$
--   so the deficit at length $n$ vanishes exactly on equal pairs, and $r_n(x,x)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/LCS.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/LCS.lean by skeleton subtraction
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

namespace OAI

/-! Basic properties of the manuscript's exact longest-common-subsequence
length. All maxima are attained by actual ordered sublists. -/
noncomputable section
namespace TreeEdit.BinaryLower

universe u
variable {α : Type u}

@[simp] theorem lcs_nil_left (x : List α) : lcs [] x = 0 :=
  Nat.eq_zero_of_le_zero (lcs_le_length_left [] x)

@[simp] theorem lcs_nil_right (x : List α) : lcs x [] = 0 :=
  Nat.eq_zero_of_le_zero (lcs_le_length_right x [])

theorem lcs_eq_length_iff {x y : List α} (hlen : x.length = y.length) :
    lcs x y = x.length ↔ x = y := by
  constructor
  · intro h
    obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
    have hzx : z = x := hx.eq_of_length (hz.trans h)
    subst z
    exact hy.eq_of_length hlen
  · rintro rfl
    exact lcs_self _

theorem deficit_eq_zero_iff {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    deficit n x y = 0 ↔ x = y := by
  rw [deficit, Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    apply (lcs_eq_length_iff (hx.trans hy.symm)).mp
    have depth := lcs_le_length_left x y
    omega
  · rintro rfl
    simp [hx]

@[simp] theorem deficit_self {n : ℕ} {x : List α} (hx : x.length = n) :
    deficit n x x = 0 := (deficit_eq_zero_iff hx hx).mpr rfl

end TreeEdit.BinaryLower

end

end OAI


