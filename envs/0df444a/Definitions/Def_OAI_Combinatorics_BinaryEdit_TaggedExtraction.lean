-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
-- name    : OAI_Combinatorics_BinaryEdit_TaggedExtraction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:59:11.321352+00:00
-- url     : https://prove2.me/theorems/726c9e66-1fd1-4f03-9a40-71339c283e72
-- title:
--   Rows of equal-width blocks
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. Let $B$ be a block width.
--
--   1. **Blocks.** For $X_1,\dots,X_m$ words of length $B$, the concatenation $X_1X_2\cdots X_m$ of length $mB$.
--   2. **Rows.** For a $T\times m$ array of blocks $X_{a,i}$, the concatenation of the $T$ rows, of length $TmB$. Position $a\,mB+iB+j$ is the $j$-th letter of block $(a,i)$, and a position $t$ lies in row
--   $$
--   \bigl\lfloor\lfloor t/B\rfloor/m\bigr\rfloor<T .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedExtraction.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedExtraction.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower
namespace TaggedExtraction

universe u
variable {α : Type u}

/-- A row obtained by concatenating equal-width blocks in increasing index order. -/
def blocks {m B : ℕ} (X : Fin m → Word α B) : List α :=
  (List.finRange m).flatMap fun i => (X i).val

lemma blocks_succ {m B : ℕ} (X : Fin (m + 1) → Word α B) :
    blocks X = (X 0).val ++ blocks (fun i => X i.succ) := by
  simp [blocks, List.finRange_succ, List.flatMap_map]

@[simp] lemma length_blocks {m B : ℕ} (X : Fin m → Word α B) :
    (blocks X).length = m * B := by
  induction m with
  | zero => simp [blocks]
  | succ m ih =>
    rw [blocks_succ]
    simp only [List.length_append, (X 0).property, ih]
    ring

lemma block_index_lt {m B : ℕ} (i : Fin m) (j : Fin B) :
    i.val * B + j.val < m * B := by
  calc
    i.val * B + j.val < i.val * B + B := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * B := by ring
    _ ≤ m * B := Nat.mul_le_mul_right B i.isLt

/-- `T` rows of `m` blocks of width `B`. -/
def rows {T m B : ℕ} (X : Fin T → Fin m → Word α B) : List α :=
  blocks fun a => ⟨blocks (X a), length_blocks (X a)⟩

@[simp] lemma length_rows {T m B : ℕ} (X : Fin T → Fin m → Word α B) :
    (rows X).length = T * m * B := by
  simp only [rows, length_blocks]
  ring

lemma row_index_lt {T m B : ℕ} (a : Fin T) (i : Fin m) (j : Fin B) :
    a.val * (m * B) + (i.val * B + j.val) < T * m * B := by
  simpa only [Nat.mul_assoc] using
    block_index_lt a (⟨i.val * B + j.val, block_index_lt i j⟩ : Fin (m * B))

lemma row_quotient_lt {T m B p : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hp : p < T * m * B) : p / B / m < T := by
  rw [Nat.div_lt_iff_lt_mul hm]
  exact (Nat.div_lt_iff_lt_mul hB).2 hp

end TaggedExtraction
end TreeEdit.BinaryLower

end

end OAI


