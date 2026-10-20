-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
-- name    : OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:36:34.704345+00:00
-- url     : https://prove2.me/theorems/8ba45fe9-0152-44af-bf11-1726bfe2e361
-- title:
--   Leaves, cyclic states and tagged symbols
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Fix periods $Q(l)$ for the leaves $l$.
--
--   1. **Leaves.** Paths of exactly $k$ edges in the $m$-ary tree.
--   2. **States and symbols.** The state group $\prod_l\mathbb Z/Q(l)$, and the tagged alphabet
--   $$
--   \Gamma=\{(l,r):\ l\text{ a leaf},\ r\in\mathbb Z/Q(l)\}.
--   $$
--   3. **Leaf decoder.** At a leaf $l$ with state $x$, the symbol $(l,x_l)$, which records the leaf and its own coordinate.
--   4. **Relabeling.** The equivalence between list paths and functions $\{1..k\}\to\{1..m\}$, and the induced pullback of states.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BinaryEditLower mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords

namespace OAI

/-! Concrete tagged leaf states and subtree locality for the finite tree. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- The finite leaf set, represented by ordered paths of exactly `k` edges. -/
abbrev Leaf (m k : ℕ) := Word (Fin m) k

/-- The manuscript's product of cyclic leaf coordinates. -/
abbrev State {m k : ℕ} (Q : Leaf m k → ℕ) := ∀ l, ZMod (Q l)

/-- A symbol retains both its leaf tag and its cyclic state. -/
abbrev Symbol {m k : ℕ} (Q : Leaf m k → ℕ) := Σ l, ZMod (Q l)

/-- Decode an actual leaf path. The fallback only totalizes this function on
paths of the wrong length; the root construction never evaluates that branch. -/
def leafDecoder {m k : ℕ} (Q : Leaf m k → ℕ) (base : Leaf m k)
    (p : List (Fin m)) (x : State Q) : Symbol Q :=
  if hp : p.length = k then ⟨⟨p, hp⟩, x ⟨p, hp⟩⟩ else ⟨base, x base⟩

@[simp] theorem leafDecoder_of_length {m k : ℕ} (Q : Leaf m k → ℕ)
    (base : Leaf m k) (p : List (Fin m)) (hp : p.length = k) (x : State Q) :
    leafDecoder Q base p x = ⟨⟨p, hp⟩, x ⟨p, hp⟩⟩ := by
  simp [leafDecoder, hp]

/-- The list-path and function-path presentations of the same leaf set. -/
def leafEquiv (m k : ℕ) : Leaf m k ≃ (Fin k → Fin m) :=
  Equiv.vectorEquivFin (Fin m) k

/-- Pull back a function-indexed cyclic state to the list-path presentation.
This is just relabeling coordinates, used to connect the closed-form vectors
to the list recursion. -/
def pullState {m k : ℕ} (Q : (Fin k → Fin m) → ℕ)
    (x : ∀ l, ZMod (Q l)) : State (fun l => Q (leafEquiv m k l)) :=
  fun l => x (leafEquiv m k l)

@[simp] theorem pullState_add {m k : ℕ} (Q : (Fin k → Fin m) → ℕ)
    (x y : ∀ l, ZMod (Q l)) :
    pullState Q (x + y) = pullState Q x + pullState Q y := rfl

@[simp] theorem pullState_nsmul {m k : ℕ} (Q : (Fin k → Fin m) → ℕ)
    (n : ℕ) (x : ∀ l, ZMod (Q l)) :
    pullState Q (n • x) = n • pullState Q x := rfl

@[simp] theorem pullState_zsmul {m k : ℕ} (Q : (Fin k → Fin m) → ℕ)
    (n : ℤ) (x : ∀ l, ZMod (Q l)) :
    pullState Q (n • x) = n • pullState Q x := rfl

end TreeEdit.BinaryLower.FiniteTree

end

end OAI


