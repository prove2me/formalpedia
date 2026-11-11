-- Prove2me | Definitions.Def_TernarySync_Alphabet_SyncString
-- name    : TernarySync_Alphabet_SyncString
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:52:01.236001+00:00
-- url     : https://prove2.me/theorems/aee9ca54-0fb3-4ffd-9940-287b87375ff9
-- title:
--   $\varepsilon$-synchronization strings (Definition 1.1), squares and square-free words (Definition 2.1)
-- statement:
--   Let $\alpha$ be an alphabet and $\varepsilon$ a real number (the paper takes $0 \le \varepsilon < 1$). A word $S \in \alpha^n$ is an **$\varepsilon$-synchronization string** (Definition 1.1) if for every $1 \le i < j < k \le n+1$
--
--   $$\mathrm{ED}\big(S[i,j),\, S[j,k)\big) > (1-\varepsilon)(k-i),$$
--
--   where $\mathrm{ED}$ is the insertion–deletion distance. The number $1-\varepsilon$ is the **synchronization gap**. So every two adjacent intervals of $S$ are far apart in edit distance, relative to their combined length, at every boundary and every scale.
--
--   A **square** (Definition 2.1) is a nonempty word repeated twice consecutively, $XX$. A word is **square-free** if none of its factors (contiguous subwords) is a square.
--
--   **Formalization Note.** `IsSyncString ε S` quantifies over 0-based indices $i < j < k \le |S|$ and uses `factor S i j`, `factor S j k` from the edit-distance definition; this is the paper's condition after the shift $i \mapsto i-1$ (the difference $k-i$ is unchanged). The inequality is strict and compares reals. The range $0 \le \varepsilon < 1$ is not built into the predicate: every statement using it states that range explicitly. `IsSquareWord w` says $w = XX$ with $X \ne []$; `IsSquareFree S` says that no infix (`<:+:`, a contiguous factor) of $S$ is a square.
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), p. 1 (PDF 2), Definition 1.1; p. 13 (PDF 14), Definition 2.1

import Mathlib
import Definitions.Def_TernarySync_Alphabet_EditDistance

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Definition 1.1 (Xu, Fu, Qiao, Tao, p. 1): a word `S` of length `n` is an
`ε`-synchronization string if for every `1 ≤ i < j < k ≤ n + 1` (1-based), equivalently every
`i < j < k ≤ n` (0-based, as here), `ED(S[i, j), S[j, k)) > (1 − ε)(k − i)`. The paper's range
`0 ≤ ε < 1` is not part of the predicate; every statement that uses it states the range. -/
def IsSyncString {α : Type*} (ε : ℝ) (S : List α) : Prop :=
  ∀ i j k : ℕ, i < j → j < k → k ≤ S.length →
    (1 - ε) * ((k : ℝ) - (i : ℝ)) < (ed (factor S i j) (factor S j k) : ℝ)

/-- A square (Definition 2.1, p. 13): a nonempty word repeated twice consecutively, `XX`. -/
def IsSquareWord {α : Type*} (w : List α) : Prop :=
  ∃ X : List α, X ≠ [] ∧ w = X ++ X

/-- A square-free word (Definition 2.1, p. 13): none of its factors (contiguous subwords) is a
square. -/
def IsSquareFree {α : Type*} (S : List α) : Prop :=
  ∀ w : List α, w <:+: S → ¬ IsSquareWord w

end TernarySync.Alphabet


