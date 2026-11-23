-- Prove2me | Definitions.Def_SystemicHoldings_FEfficient_Supplement_Diversification
-- name    : SystemicHoldings_FEfficient_Supplement_Diversification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:18:13.886807+00:00
-- url     : https://prove2.me/theorems/ddd92575-098e-47f8-a461-2e87e6a9971a
-- title:
--   Example 1, (4.1), p. 11 — full diversification $Q^{\mathrm{diversified}} = \frac1T\, q b^\top$
-- statement:
--   There are $K$ assets and $N$ banks. Let $q\in\mathbb R^K$ be the vector of total initial holdings of the banking sector (entry $q_k$ is the total holding of asset $k$), and $b\in\mathbb R^N$ the vector of the banks' initial budgets. Write
--   $$
--   T=\sum_{k=1}^K q_k .
--   $$
--   **Full portfolio diversification** is the holding matrix
--   $$
--   Q^{\mathrm{diversified}} := \frac1T\, q\, b^\top \in\mathbb R^{K\times N},\qquad Q^{\mathrm{diversified}}_{k i}=\frac{b_i\,q_k}{T},
--   $$
--   in which every bank $i$ holds the market portfolio $q/T$ scaled by its own budget $b_i$. Row $k$ is asset $k$ and column $i$ is bank $i$, as in the holding matrices of the base mission's model.
--
--   When $\sum_k q_k=\sum_i b_i=T\neq 0$, the matrix lies in the feasible set $\mathscr D(q,b)$: its rows sum to $q$ and its columns sum to $b^\top$. It is the benchmark against which Theorem 4.2 compares the f-efficient holdings.
--
--   **Formalization Note** The definition is `(1 / ∑ k, q k) • vecMulVec q b`. It divides by $T=\sum_k q_k$ (the paper's $\mathbf 1_K^\top q$, the form used in the proof of Theorem 4.2) rather than by $\sum_i b_i$; the two agree whenever $\mathscr D(q,b)\neq\emptyset$. Lean's convention $1/0=0$ makes the matrix zero when $T=0$, where the paper's object is undefined; every theorem using it assumes $T\neq0$. All other objects ($G$, $\mathscr D$, MSD, f-efficiency, $z$, $y^*$) are the published `SystemicHoldings.FEfficient.Model`.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, p. 11, Example 1, display (4.1)

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient.Supplement
open Matrix

/-- Full diversification, Example 1, display (4.1), p. 11 (Awiszus–Capponi–Weber, arXiv:2003.10121v3):
`Q^diversified := (1/T) q bᵀ ∈ ℝ^{K×N}` with `T = ∑_k q_k`, i.e. entry `(k, i)` is `b_i q_k / T`.
Every bank holds the market portfolio `q / T`, scaled by its budget `b_i`. The quotient by
`T` presupposes `T ≠ 0`, which the theorems using this definition assume. -/
noncomputable def qDiversified {K N : ℕ} (q : Fin K → ℝ) (b : Fin N → ℝ) :
    Matrix (Fin K) (Fin N) ℝ :=
  (1 / ∑ k, q k) • vecMulVec q b

end SystemicHoldings.FEfficient.Supplement


