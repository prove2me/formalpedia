-- Prove2me | Definitions.Def_SpencerEight_Supplement_word
-- name    : SpencerEight_Supplement_word
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:49:44.398421+00:00
-- url     : https://prove2.me/theorems/04f51c9b-2662-42fd-a414-4a2e5e12e2bd
-- title:
--   Kronecker word $L_1L_2\cdots L_k$
-- statement:
--   A word $L_1L_2\cdots L_k$ of $k$ letters denotes the Kronecker product of its letters in the displayed order,
--   $$
--   L_1\otimes L_2\otimes\cdots\otimes L_k\in\mathbb R^{2^k\times2^k}.
--   $$
--   Every word is a signed permutation matrix; a word with an even number of letters $J$ is symmetric and squares to the identity.
--
--   **Formalization Note** Rows and columns are indexed by $\{0,\dots,2^k-1\}$ in the standard Kronecker order: an index is read in binary with $k$ digits, and the most significant digit belongs to the leftmost letter (the outermost factor). The entry is the product over $t$ of the entries of $L_t$ at the $t$-th digits of the row and column indices.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 15.2, p.289 (PDF p.289)

import Mathlib
import Definitions.Def_SpencerEight_Supplement_Letter

namespace SpencerEight.Supplement

/-- A word of `k` letters (Section 15.2, Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.289 (PDF p.289)): the Kronecker product
`L₁ ⊗ L₂ ⊗ ⋯ ⊗ L_k` of its letters in the displayed order, a real `2^k × 2^k` matrix.

**Formalization Note** Rows and columns are indexed by `Fin (2^k)` in the standard Kronecker order: the
index `i` is read in binary with `k` digits, the most significant digit belonging to the leftmost letter
`w 0` (the outermost factor). The entry at `(i, j)` is the product over `t` of the entries of the letter
`w t` at the `t`-th binary digits of `i` and `j`, which is the entry of the iterated Kronecker product. -/
def word {k : ℕ} (w : Fin k → Letter) : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ :=
  fun i j => ∏ t : Fin k,
    (w t).mat ⟨i.val / 2 ^ (k - 1 - t.val) % 2, Nat.mod_lt _ (by norm_num)⟩
      ⟨j.val / 2 ^ (k - 1 - t.val) % 2, Nat.mod_lt _ (by norm_num)⟩

end SpencerEight.Supplement


