-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
-- name    : OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:52:27.615784+00:00
-- url     : https://prove2.me/theorems/1f7f5619-7468-4562-8af2-e5533105f768
-- title:
--   Edit scripts and basic properties of edit distance
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$.
--
--   1. **Edit scripts.** A single step inserts, deletes or substitutes one letter anywhere. A script of $n$ steps can be reversed, and two scripts can be concatenated. Erasing $x$ letter by letter is a script of length $|x|$, so scripts always exist.
--   2. **Edit distance.** $\mathrm{ed}(x,y)$ is the least length of a script, attained by some script. It is symmetric, zero iff $x=y$, and
--   $$
--   \mathrm{lcs}(x,y)\le\min(|x|,|y|),\qquad\mathrm{lcs}(x,x)=|x| .
--   $$
--   Longest common subsequences are attained, and block encodings satisfy $|c(x)|=P|x|$ and $c(xy)=c(x)c(y)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/EditMetric.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/EditMetric.lean by skeleton subtraction
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

namespace OAI

namespace TreeEdit

universe u v

namespace EditStep

variable {α : Type u} {x y : List α}

protected theorem symm (h : EditStep x y) : EditStep y x := by
  cases h with
  | insert p q a => exact .delete p q a
  | delete p q a => exact .insert p q a
  | substitute p q a b => exact .substitute p q b a

end EditStep

namespace EditScript

variable {α : Type u} {x y z : List α} {m n : ℕ}

protected theorem trans (h : EditScript x y m) (g : EditScript y z n) :
    EditScript x z (m + n) := by
  induction h with
  | nil => simpa using g
  | cons h h' ih => simpa [Nat.add_right_comm] using EditScript.cons h (ih g)

protected theorem one (h : EditStep x y) : EditScript x y 1 :=
  .cons h (.nil y)

protected theorem symm (h : EditScript x y n) : EditScript y x n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact ih.trans (.one h.symm)

protected theorem erase (x : List α) : EditScript x [] x.length := by
  induction x with
  | nil => exact .nil []
  | cons a x ih => exact .cons (.delete [] x a) ih

theorem exists_length (x y : List α) : ∃ n, EditScript x y n :=
  ⟨_, (EditScript.erase x).trans (EditScript.erase y).symm⟩

theorem zero_iff : EditScript x y 0 ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

end EditScript

variable {α : Type u} {x y z : List α}

theorem ed_script (x y : List α) : EditScript x y (ed x y) :=
  Nat.sInf_mem (EditScript.exists_length x y)

theorem ed_le_of_script {n : ℕ} (h : EditScript x y n) : ed x y ≤ n := Nat.sInf_le h

@[simp] theorem ed_self (x : List α) : ed x x = 0 :=
  Nat.eq_zero_of_le_zero (ed_le_of_script (.nil x))

@[simp] theorem ed_eq_zero_iff : ed x y = 0 ↔ x = y := by
  constructor
  · intro h
    have := ed_script x y
    rw [h] at this
    exact EditScript.zero_iff.mp this
  · rintro rfl; exact ed_self _

theorem ed_comm (x y : List α) : ed x y = ed y x := by
  apply Nat.le_antisymm
  · exact ed_le_of_script (ed_script y x).symm
  · exact ed_le_of_script (ed_script x y).symm

theorem common_lengths_nonempty (x y : List α) :
    Set.Nonempty {n : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = n} :=
  ⟨0, [], List.nil_sublist _, List.nil_sublist _, rfl⟩

theorem common_lengths_bounded (x y : List α) :
    BddAbove {n : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = n} := by
  refine ⟨x.length, ?_⟩
  rintro n ⟨z, hx, _, rfl⟩
  exact hx.length_le

theorem exists_lcs (x y : List α) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = lcs x y :=
  Nat.sSup_mem (common_lengths_nonempty x y) (common_lengths_bounded x y)

theorem length_le_lcs (hx : z.Sublist x) (hy : z.Sublist y) : z.length ≤ lcs x y :=
  le_csSup (common_lengths_bounded x y) ⟨z, hx, hy, rfl⟩

theorem lcs_le_length_left (x y : List α) : lcs x y ≤ x.length := by
  obtain ⟨z, hx, _, hz⟩ := exists_lcs x y
  exact hz ▸ hx.length_le

theorem lcs_comm (x y : List α) : lcs x y = lcs y x := by
  apply congrArg sSup
  ext n
  constructor <;> rintro ⟨z, hx, hy, hz⟩ <;> exact ⟨z, hy, hx, hz⟩

theorem lcs_le_length_right (x y : List α) : lcs x y ≤ y.length := by
  rw [lcs_comm]; exact lcs_le_length_left _ _

@[simp] theorem lcs_self (x : List α) : lcs x x = x.length := by
  exact Nat.le_antisymm (lcs_le_length_left x x)
    (length_le_lcs (List.Sublist.refl x) (List.Sublist.refl x))

@[simp] theorem deficit_self (x : List α) : deficit x x = 0 := by simp [deficit]

theorem length_encode {P : ℕ} {β : Type v} (c : α → Word β P) (x : List α) :
    (encode c x).length = x.length * P := by
  induction x with
  | nil => simp [encode]
  | cons a x ih =>
      change ((c a).val ++ encode c x).length = (x.length + 1) * P
      rw [List.length_append, (c a).property, ih]
      ring

@[simp] theorem encode_append {P : ℕ} {β : Type v} (c : α → Word β P) (x y : List α) :
    encode c (x ++ y) = encode c x ++ encode c y := by simp [encode]

@[simp] theorem encode_cons {P : ℕ} {β : Type v} (c : α → Word β P) (a : α) (x : List α) :
    encode c (a :: x) = (c a).val ++ encode c x := by simp [encode]

end TreeEdit

end OAI


