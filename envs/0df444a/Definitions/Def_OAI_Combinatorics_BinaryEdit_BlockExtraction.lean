-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
-- name    : OAI_Combinatorics_BinaryEdit_BlockExtraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:03:01.353432+00:00
-- url     : https://prove2.me/theorems/b45fcb65-0759-47f8-9ad1-7eb84edd4d85
-- title:
--   Concatenations of fixed-width blocks
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $B$ be a block width.
--
--   1. **Concatenation.** For blocks $X_1,\dots,X_n$ of length $B$, their concatenation, of length $nB$; a list of words all of length $B$ flattens to length (number of words)$\cdot B$.
--   2. **Row word.** The concatenation of $m$ blocks viewed as a word of length $mB$.
--   3. **Row concatenation.** For a $T\times m$ array,
--   $$
--   \mathop{\big\Vert}_{a<T}\ \mathop{\big\Vert}_{i<m}X_{a,i},
--   $$
--   of length $T(mB)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/BlockExtraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/BlockExtraction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction

namespace OAI

/-! Exact contiguous-window extraction from fixed-width block concatenations. -/

namespace TreeEdit.BinaryLower
namespace BlockExtraction

/-- A list of fixed-width blocks has the expected total length. -/
theorem length_flatten_fixed {α : Type*} (blocks : List (List α)) (B : ℕ)
    (hB : ∀ z ∈ blocks, z.length = B) : blocks.flatten.length = blocks.length * B := by
  induction blocks with
  | nil => simp
  | cons z zs ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hB
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      rw [hB.1, ih hB.2]
      ring

/-- The expected length for a finite indexed family of fixed-width blocks. -/
theorem length_flatten_ofFn {α : Type*} {n B : ℕ} (blocks : Fin n → Word α B) :
    (List.ofFn (fun i => (blocks i).val)).flatten.length = n * B := by
  rw [length_flatten_fixed _ B]
  · simp
  · intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact (blocks i).property

/-- The finite-range flatMap presentation used for rows in the manuscript. -/
def concatenate {α : Type*} {n B : ℕ} (blocks : Fin n → Word α B) : List α :=
  (List.finRange n).flatMap (fun i => (blocks i).val)

@[simp] theorem length_concatenate {α : Type*} {n B : ℕ}
    (blocks : Fin n → Word α B) : (concatenate blocks).length = n * B := by
  simpa only [concatenate, List.flatMap_def, ← List.ofFn_eq_map] using
    length_flatten_ofFn blocks

/-- A row is itself a word of width mB. -/
def rowWord {α : Type*} {m B : ℕ} (blocks : Fin m → Word α B) : Word α (m * B) :=
  ⟨concatenate blocks, length_concatenate blocks⟩

/-- Concatenation of a finite ordered array of fixed-width blocks. -/
def concatenateRows {α : Type*} {T m B : ℕ}
    (blocks : Fin T → Fin m → Word α B) : List α :=
  (List.finRange T).flatMap fun a =>
    (List.finRange m).flatMap fun i => (blocks a i).val

@[simp] theorem length_concatenateRows {α : Type*} {T m B : ℕ}
    (blocks : Fin T → Fin m → Word α B) :
    (concatenateRows blocks).length = T * (m * B) := by
  exact length_concatenate (fun a => rowWord (blocks a))

end BlockExtraction
end TreeEdit.BinaryLower

end OAI


