-- Prove2me | Definitions.Def_AvgPHETH_Supplement_aPar
-- name    : AvgPHETH_Supplement_aPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:33:40.27463+00:00
-- url     : https://prove2.me/theorems/a27c249d-ac71-4035-a8d5-aec20d8dd135
-- title:
--   The index length $a_j(n)=\lfloor n/R(n)^j\rfloor$
-- statement:
--   For $j,n\in\mathbb N$,
--
--   $$a_j(n)=\Big\lfloor\frac{n}{R(n)^j}\Big\rfloor .$$
--
--   A node at depth $j-1$ of a selector tree for an input of length $n$ has its children indexed by $Y_j(n)=\{0,1\}^{a_j(n)}$, so the tree has arity $\Lambda(k,n)_j=2^{a_j(n)}$ at level $j$.
--
--   **Formalization Note** The paper defines $a_j(n)$ for active $(k,n)$ and $1\le j\le k$; the same formula is used here for all $j,n$. For $n\ge16$ one has $R(n)\ge64$, so the division is not degenerate where the construction uses it.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", p.39 (PDF 41), items 1–2

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_RPar

namespace AvgPHETH.Supplement

/-- The length parameter `a_j(n) = ⌊n / R(n)^j⌋`; `Y_j(n) = {0,1}^{a_j(n)}` is the set of child
indices of a node at depth `j − 1` of a selector tree
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Parameters", items 1–2, p.39 (PDF 41)).

**Formalization Note** The page defines `a_j(n)` for active `(k, n)` and `1 ≤ j ≤ k`; this is the same
formula for all `j, n` (Theorem 8.7 uses `a_k(n)` as a function of `n`, and only large `n` matter).
For `n ≥ 16`, `R(n) ≥ 64 > 0`, so the division is not degenerate where the construction uses it. -/
noncomputable def aPar (ε : ℕ → ℝ) (j n : ℕ) : ℕ := ⌊(n : ℝ) / RPar ε n ^ j⌋₊

end AvgPHETH.Supplement


