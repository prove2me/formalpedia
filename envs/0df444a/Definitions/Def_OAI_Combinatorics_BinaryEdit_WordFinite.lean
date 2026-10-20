-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
-- name    : OAI_Combinatorics_BinaryEdit_WordFinite
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:41:24.508828+00:00
-- url     : https://prove2.me/theorems/f5fe6b6d-8734-41f7-a79a-1eb5910e50ac
-- title:
--   Finiteness of word sets over finite alphabets
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $\alpha$ be a finite alphabet.
--
--   1. **Exact-length words.** For each $n$, the words of length exactly $n$ form a finite set, of size $|\alpha|^n$.
--   2. **Capped words.** For each $d$, the words of length at most $d$ form a finite set, inhabited by the empty word:
--   $$
--   |W_{\le d}(\alpha)|=\sum_{n=0}^d|\alpha|^n .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/WordFinite.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/WordFinite.lean by skeleton subtraction
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

namespace OAI

namespace TreeEdit.BinaryLower

universe u
variable {α : Type u}

/-- Exact-length words form a finite type over every finite alphabet. -/
instance wordFinite [Finite α] (n : ℕ) : Finite (Word α n) :=
  inferInstanceAs (Finite (List.Vector α n))

/-- At-most-length words form a finite type; the length is retained as a
finite sigma index, so repetitions and the empty word are included. -/
instance wordsLEFinite [Finite α] (d : ℕ) : Finite (WordsLE α d) := by
  let f : WordsLE α d → Σ n : Fin (d + 1), Word α n.val :=
    fun x => ⟨⟨x.val.length, Nat.lt_succ_of_le x.property⟩, ⟨x.val, rfl⟩⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : Σ n : Fin (d + 1), Word α n.val => z.2.val) h

/-- The empty word is included even at cap zero. -/
instance wordsLEInhabited (d : ℕ) : Inhabited (WordsLE α d) :=
  ⟨⟨[], by simp⟩⟩

end TreeEdit.BinaryLower

end OAI


