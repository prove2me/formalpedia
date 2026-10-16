-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
-- name    : OAI_Combinatorics_TreeEdit_EditMetric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:13:30.982319+00:00
-- url     : https://prove2.me/theorems/4ce24799-e746-4914-9cc9-050110007ff5
-- title:
--   Edit scripts, edit distance and longest common subsequences: basic properties
-- statement:
--   This file proves the basic properties of edit scripts, edit distance and longest common subsequences; it introduces no new objects. The notions involved are as follows. Words are finite sequences over an arbitrary alphabet $\alpha$. An *edit step* turns a word $x$ into a word $y$ by one of: inserting one symbol at any position, deleting one symbol, or replacing the symbol at one position by an arbitrary symbol. An *edit script of length $n$* from $x$ to $y$ is a chain $x=w_0\to w_1\to\cdots\to w_n=y$ of edit steps, with no restriction on the lengths of the intermediate words. The unit-cost edit distance is
--
--   $$\operatorname{ed}(x,y)=\min\{\,n\in\mathbb{N} : \text{there is an edit script of length } n \text{ from } x \text{ to } y\,\}.$$
--
--   Further, $\operatorname{lcs}(x,y)$ is the largest length of a common subsequence of $x$ and $y$, $\operatorname{def}(x,y)=|x|-\operatorname{lcs}(x,y)$, and for a code $c$ assigning to each symbol of $\alpha$ a word of length $P$ over an alphabet $\beta$, $\operatorname{enc}_c$ is the concatenation map $\operatorname{enc}_c(x_1\cdots x_\ell)=c(x_1)\cdots c(x_\ell)$.
--
--   1. **Reversal and composition of scripts.** An insertion reversed is a deletion and conversely, and replacing $a$ by $b$ reversed is replacing $b$ by $a$. Hence a script of length $n$ from $x$ to $y$ yields one of length $n$ from $y$ to $x$; scripts of length $m$ from $x$ to $y$ and of length $n$ from $y$ to $z$ concatenate to a script of length $m+n$ from $x$ to $z$; and a single step is a script of length $1$.
--
--   2. **Existence and attainment.** Every word $x$ is erased by a script of length $|x|$ (delete its symbols one at a time), so a script from $x$ to $y$ always exists (erase $x$, then build $y$ by insertions). Consequently the minimum defining $\operatorname{ed}(x,y)$ is attained by a script of length exactly $\operatorname{ed}(x,y)$, and $\operatorname{ed}(x,y)\le n$ whenever a script of length $n$ exists.
--
--   3. **Identity of indiscernibles.** A script of length $0$ from $x$ to $y$ exists if and only if $x=y$; hence $\operatorname{ed}(x,x)=0$, and $\operatorname{ed}(x,y)=0$ if and only if $x=y$.
--
--   4. **Longest common subsequences.** The set of lengths of common subsequences of $x$ and $y$ contains $0$ and is bounded above by $|x|$. Hence some common subsequence has length exactly $\operatorname{lcs}(x,y)$; every common subsequence $z$ satisfies $|z|\le\operatorname{lcs}(x,y)$; $\operatorname{lcs}(x,y)\le|x|$; $\operatorname{lcs}(x,x)=|x|$; and $\operatorname{def}(x,x)=0$.
--
--   5. **Encodings.** $|\operatorname{enc}_c(x)|=|x|\,P$, $\operatorname{enc}_c(xy)=\operatorname{enc}_c(x)\operatorname{enc}_c(y)$, and $\operatorname{enc}_c(a\,x)=c(a)\operatorname{enc}_c(x)$ for a symbol $a$ and a word $x$.
--
--   Together these facts make edit distance a well-defined, attained quantity, and reversal and composition of scripts yield its symmetry and triangle inequality. They form the routine interface used whenever an explicit script is exhibited to bound edit distance from above, or a longest common subsequence is extracted to bound a deficit.
--
--   **Formalization Note** The step and script relations `EditStep` and `EditScript`, the distance `ed` (an `sInf` of natural numbers), `lcs` (an `sSup`), `deficit` and `encode` come from the shared definition files. This file contains the lemmas `EditStep.symm`, `EditScript.trans`, `EditScript.one`, `EditScript.symm`, `EditScript.erase`, `EditScript.exists_length`, `EditScript.zero_iff`, `ed_script`, `ed_le_of_script`, `ed_self`, `ed_eq_zero_iff`, `common_lengths_nonempty`, `common_lengths_bounded`, `exists_lcs`, `length_le_lcs`, `lcs_le_length_left`, `lcs_self`, `deficit_self`, `length_encode`, `encode_append` and `encode_cons`. A substitution step may replace a symbol by the same symbol.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/EditMetric.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/EditMetric.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability

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


