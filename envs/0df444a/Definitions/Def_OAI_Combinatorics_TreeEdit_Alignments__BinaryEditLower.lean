-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
-- name    : OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:53:44.79047+00:00
-- url     : https://prove2.me/theorems/3f089a7e-5925-408f-9c65-31204a62d441
-- title:
--   Alignments of words and index spans
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words.
--
--   1. **Alignment.** An alignment of size $n$ between words $x$ and $y$ consists of two increasing injections $\ell:\{1..n\}\to\{1..|x|\}$ and $r:\{1..n\}\to\{1..|y|\}$ with
--   $$
--   x_{\ell(i)}=y_{r(i)}\quad\text{for all }i ,
--   $$
--   i.e. a common subsequence together with its positions.
--   2. **Index span.** For a set $s$ of match indices, the interval from $\ell(\min s)$ to $\ell(\max s)$; empty for $s=\varnothing$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/Alignments.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/Alignments.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

structure Alignment (x y : List α) (n : ℕ) where
  left : Fin n ↪o Fin x.length
  right : Fin n ↪o Fin y.length
  agree : ∀ i, x.get (left i) = y.get (right i)

namespace Alignment

variable {n : ℕ}

end Alignment

noncomputable def indexSpan {N L : ℕ} (f : Fin N ↪o Fin L) (s : Finset (Fin N)) :
    Finset (Fin L) :=
  if h : s.Nonempty then Finset.Icc (f (s.min' h)) (f (s.max' h)) else ∅

@[simp] theorem indexSpan_empty {N L : ℕ} (f : Fin N ↪o Fin L) :
    indexSpan f ∅ = ∅ := by simp [indexSpan]

end TreeEdit

end OAI


