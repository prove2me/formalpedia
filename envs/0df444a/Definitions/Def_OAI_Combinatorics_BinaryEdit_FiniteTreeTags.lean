-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
-- name    : OAI_Combinatorics_BinaryEdit_FiniteTreeTags
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:44:58.295181+00:00
-- url     : https://prove2.me/theorems/9315c17b-5972-4ef4-b7a5-268d18b1ae45
-- title:
--   Tagged alphabets below tree nodes
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$.
--
--   1. **Subtree alphabet.** For a node $p$, the set of tagged symbols whose leaf tag extends $p$:
--   $$
--   \Gamma_p=\{(l,r):\ p\text{ is a prefix of }l\}.
--   $$
--   Every symbol of a node word at $p$ lies in $\Gamma_p$, and distinct children $p\,i\ne p\,i'$ have disjoint alphabets. This is the disjointness needed by the row lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeTags.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeTags.lean by skeleton subtraction
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

namespace OAI

/-!
# Concrete tagged alphabets below finite-tree nodes

The generic row lemma needs disjoint alphabets for distinct children. Here
that hypothesis is proved for the actual tagged cyclic-state symbols, not
postulated as an additional property of the construction.
-/

namespace TreeEdit.BinaryLower.FiniteTree

/-- The actual alphabet below a prefix consists of tagged leaf residues. -/
def subtreeAlphabet {m k : ℕ} (Q : Leaf m k → ℕ) (p : List (Fin m)) :
    Set (Symbol Q) := {s | p <+: s.1.val}

end TreeEdit.BinaryLower.FiniteTree

end OAI


