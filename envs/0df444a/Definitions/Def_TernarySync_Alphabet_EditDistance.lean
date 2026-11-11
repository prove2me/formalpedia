-- Prove2me | Definitions.Def_TernarySync_Alphabet_EditDistance
-- name    : TernarySync_Alphabet_EditDistance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:51:22.559856+00:00
-- url     : https://prove2.me/theorems/a802c3b2-9d31-4b1e-98b0-341cc743dce2
-- title:
--   Insertion–deletion distance ED, longest common subsequence LCS, and factors $S[i,j)$
-- statement:
--   Words are finite sequences over an alphabet $\alpha$. An **edit step** of the insertion–deletion channel turns a word $x$ into a word $y$ by inserting one symbol ($x = uv$, $y = uav$) or by deleting one symbol ($x = uav$, $y = uv$), where $u, v$ are words and $a \in \alpha$; substitutions are *not* edit steps. The **insertion–deletion distance** is
--
--   $$\mathrm{ED}(x,y) = \min\{\, n \ge 0 : x \text{ can be transformed into } y \text{ by } n \text{ insertions and deletions} \,\}.$$
--
--   The minimum exists: deleting all symbols of $x$ and inserting all symbols of $y$ takes $|x| + |y|$ steps. The **longest common subsequence length** $\mathrm{LCS}(x,y)$ is the largest length of a word $z$ that is a (not necessarily contiguous) subsequence of both $x$ and $y$; it is at most $\min(|x|,|y|)$.
--
--   For a word $S = S_1 \cdots S_n$ the paper writes $S[i,j) = S_i S_{i+1} \cdots S_{j-1}$ for $1 \le i \le j \le n+1$. These are the objects of §2.1 and Definition 1.1 of the paper; synchronization strings are defined through $\mathrm{ED}$ of adjacent factors.
--
--   **Formalization Note.** Words are `List α`. `IDStep x y` is one insertion or deletion; `IDScript n x y` says that $y$ is reached from $x$ by exactly $n$ steps; `ed x y` is the `sInf` of these $n$ (a nonempty set of naturals, so a true minimum); `lcs x y` is the `sSup` of the lengths of common sublists (`List.Sublist`; the set contains $0$ and is bounded by $|x|$, so a true maximum). Indices are 0-based: `factor S i j` is the list of the symbols at positions $i, \dots, j-1$, so the paper's $S[i,j)$ is `factor S (i-1) (j-1)`.
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 1 (PDF 2), before Definition 1.1; p. 13 (PDF 14), §2 and §2.1

import Mathlib

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- One edit step of the insertion–deletion channel (Xu, Fu, Qiao, Tao, §2.1, p. 13): `y` arises
from `x` by inserting one symbol (`x = u v`, `y = u a v`) or by deleting one symbol
(`x = u a v`, `y = u v`). Substitutions are not edit steps. -/
def IDStep {α : Type*} (x y : List α) : Prop :=
  (∃ u v : List α, ∃ a : α, x = u ++ v ∧ y = u ++ a :: v) ∨
    (∃ u v : List α, ∃ a : α, x = u ++ a :: v ∧ y = u ++ v)

/-- `IDScript n x y`: the word `x` is transformed into `y` by a chain of exactly `n` single-symbol
insertions and deletions. -/
inductive IDScript {α : Type*} : ℕ → List α → List α → Prop
  | refl (x : List α) : IDScript 0 x x
  | step {n : ℕ} {x y z : List α} : IDStep x y → IDScript n y z → IDScript (n + 1) x z

/-- The insertion–deletion distance `ED(x, y)`: the minimum number of symbol insertions and
deletions transforming `x` into `y` (§2.1, p. 13). The set of script lengths is never empty
(delete every symbol of `x`, then insert every symbol of `y`), so the infimum is a minimum. -/
noncomputable def ed {α : Type*} (x y : List α) : ℕ :=
  sInf {n : ℕ | IDScript n x y}

/-- The longest common subsequence length `LCS(x, y)`: the largest length of a word that is a
(not necessarily contiguous) subsequence of both `x` and `y` (§2.1, p. 13). The set of such
lengths contains `0` and is bounded by the length of `x`, so the supremum is a maximum. -/
noncomputable def lcs {α : Type*} (x y : List α) : ℕ :=
  sSup {k : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k}

/-- The factor `S[i, j)` in 0-based indexing: the symbols of `S` at positions `i, …, j − 1`.
The paper's 1-based factor `S[i, j) = S_i ⋯ S_{j−1}` (`1 ≤ i ≤ j ≤ n + 1`) is
`factor S (i − 1) (j − 1)`. -/
def factor {α : Type*} (S : List α) (i j : ℕ) : List α :=
  (S.drop i).take (j - i)

end TernarySync.Alphabet


