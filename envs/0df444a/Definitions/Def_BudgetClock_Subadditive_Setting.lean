-- Prove2me | Definitions.Def_BudgetClock_Subadditive_Setting
-- name    : BudgetClock_Subadditive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:23:48.530772+00:00
-- url     : https://prove2.me/theorems/e4848f97-cf93-4eb7-adb3-68e336db85dd
-- title:
--   §2, p. 5 — subadditive valuation functions on a finite set of bidders
-- statement:
--   Let $N = \{1,\dots,n\}$ be a finite set of $n$ bidders and let $v : 2^N \to \mathbb{R}$ be a set function assigning a value $v(S)$ to every subset $S \subseteq N$. The function $v$ is **subadditive** if for all $S, T \subseteq N$
--
--   $$v(S \cup T) \le v(S) + v(T).$$
--
--   This is the class of valuation functions of §5 of the paper. It contains all XOS (fractionally subadditive) and all non-negative submodular functions. Neither monotonicity nor the normalization $v(\emptyset) = 0$ is part of the definition, since the paper assumes neither.
--
--   **Formalization Note** The bidders are `Fin n` and subsets are `Finset (Fin n)`; the predicate is `IsSubadditive v`. Non-negativity of $v$ (the codomain $\mathbb{R}_{\ge 0}$ of §2) is stated as a separate hypothesis wherever it is used.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 5, §2 Preliminaries (definition of subadditive valuations)

import Mathlib

namespace BudgetClock.Subadditive

/-- §2, p. 5: a set function `v : 2^N → ℝ` on the bidders `N = Fin n` is *subadditive* if
`v (S ∪ T) ≤ v S + v T` for all `S, T ⊆ N`. Neither monotonicity nor `v ∅ = 0` is assumed. -/
def IsSubadditive {n : ℕ} (v : Finset (Fin n) → ℝ) : Prop :=
  ∀ S T : Finset (Fin n), v (S ∪ T) ≤ v S + v T

end BudgetClock.Subadditive


