-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
-- name    : OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:39:01.91191+00:00
-- url     : https://prove2.me/theorems/a1d9b2ab-a747-4255-a674-af50f8d174e8
-- title:
--   Subtree vectors vanish off their subtree
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let $u_j(a)$ and $w_j(a)$ be the subtree vectors at depth $j$ for the leaf $a$, in the state group $\prod_b\mathbb Z/Q(b)$.
--
--   1. **Support.** If the leaf $b$ does not agree with $a$ to depth $j$, then
--   $$
--   u_j(a)_b=0\qquad\text{and}\qquad w_j(a)_b=0 .
--   $$
--   So both vectors are supported on the leaves of the subtree at depth $j$ through $a$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteVectorRestrictions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteVectorRestrictions.lean by skeleton subtraction
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

namespace OAI

/-! Coordinate restrictions of the finite subtree vectors. -/

namespace TreeEdit.BinaryLower.FiniteVectors

variable {m k : ℕ}

@[simp] theorem u_off_subtree (p : Fin k → Fin m → ℕ) (j : ℕ)
    (a b : Leaf m k) (hab : ¬ Agrees j a b) : u p j a b = 0 := by
  simp [u, hab]

@[simp] theorem w_off_subtree (p : Fin k → Fin m → ℕ) (j : ℕ)
    (a b : Leaf m k) (hab : ¬ Agrees j a b) : w p j a b = 0 := by
  simp [w, hab]

end TreeEdit.BinaryLower.FiniteVectors

end OAI


