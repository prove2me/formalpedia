-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
-- name    : OAI_Combinatorics_BinaryEdit_FiniteVectors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:37:41.066779+00:00
-- url     : https://prove2.me/theorems/ece88417-c771-49fb-a7b0-f4011e87b6ee
-- title:
--   Prime periods and subtree vectors
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Fix integers $p(q,i)$, for levels $q<k$ and children $i<m$.
--
--   1. **Agreement.** Leaves $a,b$ agree to depth $j$ if $a_q=b_q$ for $q<j$.
--   2. **Periods.** The level product $\prod_ip(q,i)$; the suffix scale $s_j=\prod_{q\ge j}\prod_ip(q,i)$; the prefix period $2\prod_{q<j}p(q,a_q)$ and the leaf period $Q(a)=2\prod_qp(q,a_q)$.
--   3. **Subtree vectors.** In the state group $\prod_a\mathbb Z/Q(a)$,
--   $$
--   w_j(a)_b=s_j\,\mathbf 1[b\text{ agrees with }a\text{ to depth }j],\qquad u_j(a)_b=s_{j+1}\,\mathbf 1[\cdots].
--   $$
--   At a leaf, $w_k(a)$ is the unit vector of $a$; $u_j(a)$ is the cheap row-advancing vector.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteVectors.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BinaryEditLower mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Concrete vectors for the finite tree (finite-tree.tex, finite-vectors).
A prefix is represented by its depth and any full leaf path extending it.
All definitions ignore the unused tail of that representative. No primality
assumption is needed for the annihilation and recursive vector identities. -/

namespace TreeEdit.BinaryLower.FiniteVectors

open scoped BigOperators

variable {m k : ℕ}

abbrev Leaf (m k : ℕ) := Fin k → Fin m

def Agrees (j : ℕ) (a b : Leaf m k) : Prop :=
  ∀ q : Fin k, q.val < j → b q = a q

instance (j : ℕ) (a b : Leaf m k) : Decidable (Agrees j a b) :=
  inferInstanceAs (Decidable (∀ q : Fin k, q.val < j → b q = a q))

def levelProduct (p : Fin k → Fin m → ℕ) (q : Fin k) : ℕ := ∏ i, p q i

def suffixScale (p : Fin k → Fin m → ℕ) (j : ℕ) : ℕ :=
  ∏ q ∈ Finset.univ.filter (fun q : Fin k => j ≤ q.val), levelProduct p q

def prefixPeriod (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) : ℕ :=
  2 * ∏ q ∈ Finset.univ.filter (fun q : Fin k => q.val < j), p q (a q)

def leafPeriod (p : Fin k → Fin m → ℕ) (a : Leaf m k) : ℕ :=
  2 * ∏ q, p q (a q)

abbrev State (p : Fin k → Fin m → ℕ) := (a : Leaf m k) → ZMod (leafPeriod p a)

/-- Distinguished subtree vector, with the common suffix coefficient. -/
def w (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) : State p :=
  fun b => if Agrees j a b then (suffixScale p j : ZMod (leafPeriod p b)) else 0

/-- Cheap row-advancing vector. -/
def u (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) : State p :=
  fun b => if Agrees j a b then (suffixScale p (j + 1) : ZMod (leafPeriod p b)) else 0

@[simp] lemma prefixPeriod_zero (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    prefixPeriod p 0 a = 2 := by simp [prefixPeriod]

@[simp] lemma suffixScale_top (p : Fin k → Fin m → ℕ) : suffixScale p k = 1 := by
  have h : Finset.univ.filter (fun q : Fin k => k ≤ q.val) = ∅ := by
    ext q
    simp [Nat.not_le_of_gt q.isLt]
  simp [suffixScale, h]

@[simp] lemma agrees_top_iff (a b : Leaf m k) : Agrees k a b ↔ b = a := by
  constructor
  · intro h
    funext q
    exact h q q.isLt
  · rintro rfl q hq
    rfl

/-- At a leaf, the distinguished vector is the coordinate unit vector. -/
theorem w_leaf (p : Fin k → Fin m → ℕ) (a b : Leaf m k) :
    w p k a b = if b = a then 1 else 0 := by
  simp [w]

@[simp] lemma prefixPeriod_top (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    prefixPeriod p k a = leafPeriod p a := by
  simp [prefixPeriod, leafPeriod]

end TreeEdit.BinaryLower.FiniteVectors

end OAI


