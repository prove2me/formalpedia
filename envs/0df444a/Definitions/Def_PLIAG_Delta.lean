-- Prove2me | Definitions.Def_PLIAG_Delta
-- name    : PLIAG_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:27.07968+00:00
-- url     : https://prove2.me/theorems/59e6ea4f-c541-4c91-9a0c-ad0b08c124f8
-- title:
--   Delayed error term $\Delta_k=L\,\ell(\tau+1)\sum_{j=k-\tau}^kD_w(x_{j+1},x_j)$
-- statement:
--   For a sequence $\{x_k\}$, the **delayed error term** of Lemma 4.1 is
--
--   $$
--   \Delta_k:=L\cdot\ell(\tau+1)\sum_{j=k-\tau}^{k}D_w(x_{j+1},x_j),
--   $$
--
--   with $L=\max_k\sum_{j\in\mathcal J_k}L_j$, $\ell$ the function of B4 and $\tau$ the delay bound.
--
--   **Formalization Note** The range is $\{\max(k-\tau,0),\dots,k\}$ (truncated subtraction). For $k<\tau$ the paper's terms with negative index are $D_w(x_0,x_0)=0$ by the convention $x_j=x_0$ for $j<0$, so omitting them changes nothing. Values are in `EReal`.
-- source:
--   Zhang, Dai, Guo, Peng, Proximal-Like Incremental Aggregated Gradient Method with Linear Convergence under Bregman Distance Growth Conditions, arXiv:1711.01136v3, Lemma 4.1, p.11

import Mathlib
import Definitions.Def_PLIAG_bregman
import Definitions.Def_PLIAG_Lmax

namespace PLIAG

/-- **The delayed error term `Δ_k`** (Zhang–Dai–Guo–Peng, arXiv:1711.01136v3, Lemma 4.1, p.11):
`Δ_k := L · ℓ(τ + 1) Σ_{j=k−τ}^{k} D_w(x_{j+1}, x_j)`, `L = max_k Σ_{j ∈ J_k} L_j`.

**Formalization Note.** The range is `Finset.Icc (k − τ) k` with truncated subtraction. For
`k < τ` the paper's terms with negative `j` are `D_w(x_0, x_0) = 0` (convention `x_j = x_0` for
`j < 0`); they are absent here, which changes nothing. Values are `EReal`. -/
noncomputable def Delta {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal) (Lc : Fin N → ℝ)
    (J : ℕ → Finset (Fin N)) (ℓ : ℕ → ℝ) (τ : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    EReal :=
  ((Lmax Lc J * ℓ (τ + 1) : ℝ) : EReal) *
    ∑ j ∈ Finset.Icc (k - τ) k, bregman w (x (j + 1)) (x j)

end PLIAG


