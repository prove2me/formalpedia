-- Prove2me | Definitions.Def_AvgPHETH_Supplement_CVar
-- name    : AvgPHETH_Supplement_CVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:35:31.066717+00:00
-- url     : https://prove2.me/theorems/671f836c-190d-4998-acc9-7459bfef6fb1
-- title:
--   Names of the construction variables $B^k_x$, $S^k_x$, $S^k_{x,y_1,\dots,y_j}$
-- statement:
--   The selector trees of the oracle construction are determined by variables: for a string $x$ and $k\ge1$, the **root bit** $B^k_x$ over $\{0,1\}$, the **root selector** $S^k_x$ over $Y_1$, and, for each internal node $(y_1,\dots,y_j)$ of the selector tree $T^k_x$ with $1\le j<k$, the **selector** $S^k_{x,y_1,\dots,y_j}$ over $Y_{j+1}$.
--
--   This type consists of the names of such variables: a level $k$, a string $x$, a flag saying whether the variable is a root bit, and the node $(y_1,\dots,y_j)$ (empty for the root).
--
--   **Formalization Note** The names that are variables of the construction are singled out by a separate validity predicate. Every value is stored as a binary string: a root bit $b$ as the one-bit string $b$, a selector as an element of $\{0,1\}^{a_{j+1}(|x|)}$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Construction variables", p.39 (PDF 41)

import Mathlib

namespace AvgPHETH.Supplement

/-- A (name of a) **construction variable** of the oracle construction
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §8.1, "Construction variables", p.39 (PDF 41)): for a string `x` and `k ≥ 1`,
the root bit `B^k_x` is `⟨k, x, true, []⟩`, the root selector `S^k_x` is `⟨k, x, false, []⟩`, and the
selector `S^k_{x,y₁,…,y_j}` of the internal node `(y₁, …, y_j)` of the selector tree `T^k_x` is
`⟨k, x, false, [y₁, …, y_j]⟩`.

**Formalization Note** This is the type of all such names; the ones that are variables of the
construction (active `(k, |x|)`, a path of the right shape) are singled out by `CVar.IsValid`. Every
value of a variable is stored as a binary string: a root bit `b` as the one-bit string `[b]`, a selector
over `Y_{j+1} = {0,1}^{a_{j+1}(n)}` as that string. -/
structure CVar where
  /-- the level `k` of the oracle `V_k` -/
  k : ℕ
  /-- the input `x` whose selector tree `T^k_x` the variable belongs to -/
  x : List Bool
  /-- `true` for the root bit `B^k_x`, `false` for a selector -/
  isBit : Bool
  /-- the node `(y₁, …, y_j)` whose selector this is (`[]` for the root, and for the root bit) -/
  path : List (List Bool)

end AvgPHETH.Supplement


