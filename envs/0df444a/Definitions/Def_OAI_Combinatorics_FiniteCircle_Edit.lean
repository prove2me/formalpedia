-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
-- name    : OAI_Combinatorics_FiniteCircle_Edit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:35:45.98076+00:00
-- url     : https://prove2.me/theorems/ce526824-1b28-43ec-a569-6b2fdbc42f7e
-- title:
--   Basic facts on edit scripts, edit distance, common subsequences, block encodings and fresh padding
-- statement:
--   Fix an alphabet $\alpha$ and write $\alpha^{\ast}$ for the set of finite words over $\alpha$. An *edit step* changes a word by one insertion $uv\mapsto uav$, one deletion $uav\mapsto uv$ or one substitution $uav\mapsto ubv$ (with $u,v\in\alpha^{\ast}$ and $a,b\in\alpha$). An *edit script of length $n$* from $x$ to $y$ is a chain of $n$ edit steps leading from $x$ to $y$, and the edit distance $\operatorname{ed}(x,y)$ is the least $n$ for which such a script exists. The number $\operatorname{lcs}(x,y)$ is the largest length of a word that is a (not necessarily contiguous) subsequence of both $x$ and $y$. For a binary code $c:\alpha\to\{0,1\}^w$, the block encoding $\operatorname{enc}_c(x_1x_2\cdots x_n)=c(x_1)\,c(x_2)\cdots c(x_n)$ concatenates the codewords.
--
--   The module establishes the elementary properties of these notions and introduces one padding operation.
--
--   1. **Edit scripts.** An edit step from $x$ to $y$ can be reversed into a step from $y$ to $x$; a single step is a script of length $1$; scripts of lengths $n$ (from $x$ to $y$) and $m$ (from $y$ to $z$) compose to a script of length $n+m$ from $x$ to $z$; every script can be reversed; deleting all letters gives a script of length $|x|$ from $x$ to the empty word, and inserting them gives one from the empty word to $x$. Hence a script from $x$ to $y$ always exists, of length $|x|+|y|$.
--   2. **Edit distance.** The minimum defining $\operatorname{ed}(x,y)$ is attained, $\operatorname{ed}(x,y)\le n$ whenever a script of length $n$ exists, $\operatorname{ed}(x,x)=0$, and $\operatorname{ed}(x,y)=0$ if and only if $x=y$.
--   3. **Longest common subsequences.** The maximum defining $\operatorname{lcs}(x,y)$ is attained by a common subsequence; every common subsequence $z$ satisfies $|z|\le\operatorname{lcs}(x,y)$; $\operatorname{lcs}(x,y)\le\min(|x|,|y|)$; $\operatorname{lcs}(x,x)=|x|$ and the $\operatorname{lcs}$ with the empty word is $0$; for a letter $a$, $\operatorname{lcs}(x,ay)\le\operatorname{lcs}(x,y)+1$ and $\operatorname{lcs}(ax,ay)=\operatorname{lcs}(x,y)+1$. The unequal-length deficit $\max(|x|,|y|)-\operatorname{lcs}(x,y)$ vanishes for $y=x$.
--   4. **Block encodings.** $\operatorname{enc}_c$ sends the empty word to the empty word, $\operatorname{enc}_c(ax)=c(a)\operatorname{enc}_c(x)$, $\operatorname{enc}_c(xy)=\operatorname{enc}_c(x)\operatorname{enc}_c(y)$, and $|\operatorname{enc}_c(x)|=w\,|x|$.
--   5. **Fresh padding.** For $n\in\mathbb{N}$ and $x\in\alpha^{\ast}$, the padded word over the enlarged alphabet $\alpha\sqcup\{\bot\}$ is $x$ followed by $n-|x|$ copies of a new symbol $\bot$:
--   $$
--   \operatorname{pad}_n(x)=x\,\bot^{\,n-|x|},\qquad |\operatorname{pad}_n(x)|=n\ \text{ whenever } |x|\le n.
--   $$
--
--   These facts are the basic toolkit for every later comparison of edit distances, deficits and encodings. The padding map turns words of length at most $n$ into words of length exactly $n$, so that statements about equal-length words can be applied to all words of bounded length.
--
--   **Formalization Note** Edit steps and scripts are the inductive predicates `EditStep` and `EditScript n x y`; `editDistance` is an infimum and `lcs` a supremum of sets of natural numbers, which is why attainment (`editDistance_spec`, `lcs_exists`) is proved here. Subsequences are Lean's sublists. In `freshPad` the fresh symbol is `none` in `Option α` and the original letters are wrapped as `some a`; the count $n-|x|$ is truncated subtraction, so nothing is appended when $|x|\ge n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/Edit.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Edit.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

theorem symm (h : EditStep x y) : EditStep y x := by
  cases h with
  | insert u v a => exact .delete u v a
  | delete u v a => exact .insert u v a
  | substitute u v a b => exact .substitute u v b a

end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

theorem one (h : EditStep x y) : EditScript 1 x y := .cons h (.nil y)

theorem trans (h : EditScript n x y) (g : EditScript m y z) : EditScript (n + m) x z := by
  induction h with
  | nil => simpa using g
  | cons h _ ih => simpa only [Nat.add_right_comm] using EditScript.cons h (ih g)

theorem symm (h : EditScript n x y) : EditScript n y x := by
  induction h with
  | nil x => exact .nil x
  | cons h _ ih => exact ih.trans (one h.symm)

theorem deleteAll (x : List α) : EditScript x.length x [] := by
  induction x with
  | nil => exact .nil []
  | cons a x ih => exact .cons (.delete [] x a) ih

theorem insertAll (x : List α) : EditScript x.length [] x := (deleteAll x).symm

theorem exists_script (x y : List α) : ∃ n, EditScript n x y :=
  ⟨x.length + y.length, (deleteAll x).trans (insertAll y)⟩

end EditScript

theorem editDistance_spec {α : Type*} (x y : List α) : EditScript (editDistance x y) x y := by
  exact csInf_mem (EditScript.exists_script x y)

theorem editDistance_le_of_script {α : Type*} {x y : List α} {n : ℕ} (h : EditScript n x y) :
    editDistance x y ≤ n := csInf_le (OrderBot.bddBelow _) h

@[simp] theorem editDistance_self {α : Type*} (x : List α) : editDistance x x = 0 :=
  Nat.eq_zero_of_le_zero (editDistance_le_of_script (.nil x))

@[simp] theorem editDistance_eq_zero {α : Type*} {x y : List α} : editDistance x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hs := editDistance_spec x y
    rw [h] at hs
    cases hs
    rfl
  · rintro rfl
    exact editDistance_self x

@[simp] theorem encode_nil {α : Type*} {w : ℕ} (c : α → Fin w → Bool) : encode c [] = [] := rfl
@[simp] theorem encode_cons {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (a : α) (x : List α) :
    encode c (a :: x) = List.ofFn (c a) ++ encode c x := rfl
@[simp] theorem encode_append {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x y : List α) :
    encode c (x ++ y) = encode c x ++ encode c y := List.flatMap_append
@[simp] theorem length_encode {α : Type*} {w : ℕ} (c : α → Fin w → Bool) (x : List α) :
    (encode c x).length = w * x.length := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem lcs_exists {α : Type*} (x y : List α) :
    ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = lcs x y := by
  let s := {n : ℕ | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = n}
  have hs : s.Nonempty := ⟨0, [], List.nil_sublist _, List.nil_sublist _, rfl⟩
  have hf : s.Finite := (Set.finite_Iic x.length).subset (by
    rintro n ⟨z, hx, _, rfl⟩
    exact hx.length_le)
  exact hs.csSup_mem hf

theorem le_lcs {α : Type*} {x y z : List α} (hx : z <+ x) (hy : z <+ y) :
    z.length ≤ lcs x y := by
  apply le_csSup
  · refine ⟨x.length, ?_⟩
    rintro n ⟨u, hu, _, rfl⟩
    exact hu.length_le
  · exact ⟨z, hx, hy, rfl⟩

theorem lcs_le_length_left {α : Type*} (x y : List α) : lcs x y ≤ x.length := by
  obtain ⟨z, hx, _, hz⟩ := lcs_exists x y
  rw [← hz]
  exact hx.length_le

theorem lcs_le_length_right {α : Type*} (x y : List α) : lcs x y ≤ y.length := by
  obtain ⟨z, _, hy, hz⟩ := lcs_exists x y
  rw [← hz]
  exact hy.length_le

@[simp] theorem lcs_self {α : Type*} (x : List α) : lcs x x = x.length :=
  Nat.le_antisymm (lcs_le_length_left _ _) (le_lcs (List.Sublist.refl _) (List.Sublist.refl _))

@[simp] theorem lcs_nil_left {α : Type*} (x : List α) : lcs [] x = 0 :=
  Nat.eq_zero_of_le_zero (lcs_le_length_left _ _)

@[simp] theorem lcs_nil_right {α : Type*} (x : List α) : lcs x [] = 0 :=
  Nat.eq_zero_of_le_zero (lcs_le_length_right _ _)

@[simp] theorem unequalDeficit_self {α : Type*} (x : List α) : unequalDeficit x x = 0 := by
  simp [unequalDeficit]

theorem lcs_cons_right_le {α : Type*} (x y : List α) (a : α) :
    lcs x (a :: y) ≤ lcs x y + 1 := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x (a :: y)
  cases hy with
  | cons _ hy => have h := le_lcs hx hy; omega
  | cons_cons _ hy =>
    have h := le_lcs ((List.Sublist.refl _).cons _ |>.trans hx) hy
    simp only [List.length_cons] at hz
    omega

@[simp] theorem lcs_cons_cons {α : Type*} (x y : List α) (a : α) :
    lcs (a :: x) (a :: y) = lcs x y + 1 := by
  apply Nat.le_antisymm
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists (a :: x) (a :: y)
    cases hx with
    | cons _ hx =>
      have h := (le_lcs hx hy).trans (lcs_cons_right_le x y a)
      omega
    | cons_cons _ hx =>
      cases hy with
      | cons _ hy =>
        have h := le_lcs hx ((List.Sublist.refl _).cons _ |>.trans hy)
        simp only [List.length_cons] at hz
        omega
      | cons_cons _ hy =>
        have h := le_lcs hx hy
        simp only [List.length_cons] at hz
        omega
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
    have h := le_lcs (hx.cons_cons a) (hy.cons_cons a)
    simp only [List.length_cons, hz] at h
    exact h

def freshPad {α : Type*} (n : ℕ) (x : List α) : List (Option α) :=
  x.map some ++ List.replicate (n - x.length) none

@[simp] theorem length_freshPad {α : Type*} {n : ℕ} {x : List α} (hx : x.length ≤ n) :
    (freshPad n x).length = n := by simp [freshPad]; omega

end FiniteCircle

end OAI


