-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
-- name    : OAI_Combinatorics_BinaryEdit_FiniteTreeWords
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:34:01.042759+00:00
-- url     : https://prove2.me/theorems/d7555f4b-3fdc-4e55-b124-e93ad7ea6bb0
-- title:
--   Recursive row words on a finite tree
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $A$ be an additive state group, $\Gamma$ an alphabet, $T,m\in\mathbb N$, $\lambda(p,x)\in\Gamma$ a leaf symbol and $u(p)\in A$ a shift vector at each node $p$.
--
--   1. **Node word.** At height $0$ the word is the single symbol $\lambda(p,x)$. At height $h+1$,
--   $$
--   \omega_{h+1}(p,x)=\mathop{\big\Vert}_{a=0}^{T-1}\ \mathop{\big\Vert}_{i=1}^{m}\ \omega_h\bigl(p\,i,\ x+a\,u(p)\bigr),
--   $$
--   a concatenation of $T$ rows of $m$ child words. Its length is $(mT)^h$.
--   2. **Row.** For fixed $x$, the concatenation of the $m$ child words $\omega_h(p\,i,x)$, of length $m(mT)^h$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeWords.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeWords.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BinaryEditLower mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model

namespace OAI

/-!
# Recursive row words for the finite tree

The recursion in equation (finite-word) uses an additive state group,
node shifts and leaf symbols. It is instantiated with the product of
cyclic groups in the manuscript.
-/

namespace TreeEdit.BinaryLower.FiniteTree

variable {A Γ : Type*} [AddCommMonoid A]

/-- A row is the ordered concatenation of the `m` child words.  At a leaf the
word consists of its single tagged state symbol. -/
def nodeWord {m : ℕ} (T : ℕ) (leaf : List (Fin m) → A → Γ)
    (u : List (Fin m) → A) : ℕ → List (Fin m) → A → List Γ
  | 0, p, x => [leaf p x]
  | h + 1, p, x => (List.range T).flatMap fun a =>
      (List.finRange m).flatMap fun i => nodeWord T leaf u h (p ++ [i]) (x + a • u p)

/-- All node words at a given height have exactly the manuscript's length. -/
@[simp] theorem nodeWord_length {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) :
    (nodeWord T leaf u h p x).length = (m * T) ^ h := by
  induction h generalizing p x with
  | zero => simp [nodeWord]
  | succ h ih =>
      simp only [nodeWord, List.length_flatMap, ih]
      simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- One row at a node of height `h+1`. -/
def nodeRow {m : ℕ} (T : ℕ) (leaf : List (Fin m) → A → Γ)
    (u : List (Fin m) → A) (h : ℕ) (p : List (Fin m)) (x : A) : List Γ :=
  (List.finRange m).flatMap fun i => nodeWord T leaf u h (p ++ [i]) x

@[simp] theorem nodeRow_length {m : ℕ} (T : ℕ)
    (leaf : List (Fin m) → A → Γ) (u : List (Fin m) → A)
    (h : ℕ) (p : List (Fin m)) (x : A) :
    (nodeRow T leaf u h p x).length = m * (m * T) ^ h := by
  simp [nodeRow, List.length_flatMap]

end TreeEdit.BinaryLower.FiniteTree

end OAI


