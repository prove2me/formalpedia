-- Prove2me | Definitions.Def_ApproxEquilibriumCost_General_PolynomialLatencies
-- name    : ApproxEquilibriumCost_General_PolynomialLatencies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:14.942567+00:00
-- url     : https://prove2.me/theorems/4bc158e2-7e1a-4c36-9416-9c97da07f7b2
-- title:
--   §2.1 — polynomial latencies of degree at most d
-- statement:
--   For a game $G$ and natural degree bound $d$, polynomial latencies mean there are real coefficients $a_{e,j}\ge0$ with
--
--   $$\ell_e(x)=\sum_{j=0}^{d}a_{e,j}x^j\quad (x\ge0).$$
--
--   All leading coefficients may vanish, and constant and identically zero resource latencies are allowed. The ratio theorems impose $d\ge1$ separately. This predicate refines the generic latency class without changing the game's resource sets, strategies or real demands.
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, §2.1 polynomial-latency class, printed p.8 = PDF p.8 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_GameModel

namespace ApproxEquilibriumCost.General

/-- Section 2.1, p.8: degree at most d with nonnegative coefficients; zero
latencies and lower degrees are allowed. Only nonnegative arguments are used. -/
def HasPolynomialLatencies {n k : ℕ} (G : Game n k) (d : ℕ) : Prop :=
  ∃ a : Fin n → Fin (d + 1) → ℝ,
    (∀ e j, 0 ≤ a e j) ∧
    ∀ e x, 0 ≤ x → G.latency e x = ∑ j, a e j * x ^ (j : ℕ)

end ApproxEquilibriumCost.General


