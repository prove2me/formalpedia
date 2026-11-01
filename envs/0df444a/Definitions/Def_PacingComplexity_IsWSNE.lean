-- Prove2me | Definitions.Def_PacingComplexity_IsWSNE
-- name    : PacingComplexity_IsWSNE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:23.532501+00:00
-- url     : https://prove2.me/theorems/5d5b49d1-6976-41e0-98d9-d2e7b5b1b2e3
-- title:
--   $\varepsilon$-well-supported Nash equilibrium of a cost bimatrix game
-- statement:
--   Let $A,B$ be $n\times n$ **cost** matrices of a bimatrix game: if player 1 plays row $i$ and player 2 plays column $j$, they pay $A_{ij}$ and $B_{ij}$. Let $\Delta_n$ be the set of probability distributions on $[n]$. A pair $(x,y)\in\Delta_n\times\Delta_n$ is an **$\varepsilon$-well-supported Nash equilibrium** if
--
--   1. $x_i>0$ implies $\sum_j A_{ij}y_j\le\sum_j A_{kj}y_j+\varepsilon$ for all $k\in[n]$, and
--   2. $y_j>0$ implies $\sum_i x_iB_{ij}\le\sum_i x_iB_{ik}+\varepsilon$ for all $k\in[n]$.
--
--   Every pure strategy a player uses has expected cost within $\varepsilon$ of the best pure strategy. This is the solution concept of the problem the hardness proof reduces from.
--
--   **Formalization Note** $\Delta_n$ is Mathlib's standard simplex; both players' conditions are included.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Appendix A, p.30 (and §3.1, p.11, for Δn and cost matrices)

import Mathlib

namespace PacingComplexity

/-- **ε-well-supported Nash equilibrium of a cost bimatrix game** (Chen, Kroer, Kumar, *The
Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2, Appendix A, p.30): "an
ε-well-supported Nash equilibrium is a pair (x, y) ∈ ∆n × ∆n such that xi > 0 for any i ∈ [n]
implies that Σ_j Aij yj ≤ Σ_j Akj yj + ε for all k and yj > 0 for any j ∈ [n] implies
Σ_i xi Bij ≤ Σ_i xi Bik + ε for all k ∈ [n]."

`A` and `B` are the **cost** matrices of players 1 and 2 (p.11: "a pair of cost matrices"; costs
are minimized): every pure strategy in the support of a player's mixed strategy has expected cost
within `ε` of every other pure strategy.

**Formalization Note** `∆n` is Mathlib's standard simplex `stdSimplex ℝ (Fin n)` (non-negative
entries summing to 1). Both players' clauses are included. -/
def IsWSNE {n : ℕ} (ε : ℝ) (A B : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) : Prop :=
  x ∈ stdSimplex ℝ (Fin n) ∧ y ∈ stdSimplex ℝ (Fin n) ∧
  (∀ i, 0 < x i → ∀ k, ∑ j, A i j * y j ≤ ∑ j, A k j * y j + ε) ∧
  (∀ j, 0 < y j → ∀ k, ∑ i, x i * B i j ≤ ∑ i, x i * B i k + ε)

end PacingComplexity


