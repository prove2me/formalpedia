-- Prove2me | Definitions.Def_OnlineSaddlePoint_Supplement_bilinearPayoff
-- name    : OnlineSaddlePoint_Supplement_bilinearPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:51:33.084565+00:00
-- url     : https://prove2.me/theorems/4e7d1d03-c113-449e-a4c2-ed3ee0221062
-- title:
--   Bilinear payoff $\bar{\mathcal L}_t(x,y)=x^\top A_t y$ of an online matrix game
-- statement:
--   In an **online matrix game** player 1 has $d_1$ actions and player 2 has $d_2$ actions, and round $t$ has a payoff matrix $A_t$ whose $(i,j)$ entry is player 1's loss and player 2's reward when they play $i$ and $j$. With mixed strategies $x\in\Delta_X\subset\mathbb R^{d_1}$, $y\in\Delta_Y\subset\mathbb R^{d_2}$ the expected payoff is
--
--   $$
--   \bar{\mathcal L}_t(x,y)=x^\top A_t y=\sum_{i=1}^{d_1}\sum_{j=1}^{d_2}x_i\,(A_t)_{ij}\,y_j .
--   $$
--
--   This definition turns a sequence of matrices into the corresponding sequence of bilinear payoff functions; it is convex-concave (in fact bilinear), so online matrix games are a special case of the online saddle point problem.
--
--   **Formalization Note** Strategies are in `PiLp 1 (fun _ : Fin d => ℝ)` ($\ell_1$ geometry). The entry bound $A_t\in[-1,1]^{d_1\times d_2}$ is a hypothesis of the theorems, not part of the definition. Index $0$ of the matrix sequence is unused.
-- source:
--   Rivera Cardoso, Wang, Xu, The Online Saddle Point Problem and Online Convex Optimization with Knapsacks, arXiv:1806.08301v3, §5, pp.15–16

import Mathlib

namespace OnlineSaddlePoint.Supplement

/-- **Bilinear payoff of an online matrix game.** Rivera Cardoso, Wang, Xu, arXiv:1806.08301v3, §5,
pp.15–16: "At each time step `t = 1, ..., T`, the payoff of the players will be given by a payoff
matrix `A_t ∈ [−1, 1]^{d₁×d₂}` … the convex-concave function is defined as `𝓛_t(x, y) = xᵀA_t y`".
Given the matrix sequence `A`, this is the payoff sequence `t ↦ (x, y) ↦ xᵀ A_t y`.

**Formalization Note.** Strategies live in `PiLp 1 (fun _ : Fin d => ℝ)` (`ℝ^d` with the `ℓ₁` norm,
the geometry of §5) and `xᵀ A_t y` is written out as `∑ i, ∑ j, x i * A t i j * y j`. The entry bound
`A_t ∈ [−1, 1]^{d₁×d₂}` is a hypothesis of each statement, not part of this definition. Index `0`
of the matrix sequence is never used. -/
def bilinearPayoff {d₁ d₂ : ℕ} (A : ℕ → Matrix (Fin d₁) (Fin d₂) ℝ) :
    ℕ → PiLp 1 (fun _ : Fin d₁ => ℝ) → PiLp 1 (fun _ : Fin d₂ => ℝ) → ℝ :=
  fun t x y => ∑ i, ∑ j, x i * A t i j * y j

end OnlineSaddlePoint.Supplement


