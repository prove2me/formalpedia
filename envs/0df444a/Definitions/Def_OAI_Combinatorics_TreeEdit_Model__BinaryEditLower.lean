-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
-- name    : OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:32:20.59955+00:00
-- url     : https://prove2.me/theorems/50ad8a22-7409-426b-bd66-b8334bd99f9f
-- title:
--   Longest common subsequences, deficits and block encodings
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words.
--
--   1. **Longest common subsequence.** $\mathrm{lcs}(x,y)$ is the largest length of a list that is a sublist of both $x$ and $y$.
--   2. **Deficit.** $\mathrm{def}(x,y)=|x|-\mathrm{lcs}(x,y)$, used for words of equal length.
--   3. **Block encoding.** For a code $c$ assigning to each letter a word of fixed length $P$, the encoding of $x=a_1\cdots a_n$ is
--   $$
--   c(a_1)\,c(a_2)\cdots c(a_n),
--   $$
--   a word of length $nP$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BinaryEditLower mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BinaryEditLower

namespace OAI

namespace TreeEdit

universe u v

/-- The length of a longest arbitrary common subsequence. -/
noncomputable def lcs {α : Type u} (x y : List α) : ℕ :=
  sSup {n | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = n}

/-- One-sided deficit; used below only when the two lengths agree. -/
noncomputable def deficit {α : Type u} (x y : List α) : ℕ := x.length - lcs x y

/-- The concatenation extension of a fixed-width symbol code, on *all* finite words. -/
def encode {α : Type u} {β : Type v} {P : ℕ} (c : α → Word β P) (x : List α) : List β :=
  x.flatMap (fun a => (c a).val)

end TreeEdit

end OAI


