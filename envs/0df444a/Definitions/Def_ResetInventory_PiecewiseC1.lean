-- Prove2me | Definitions.Def_ResetInventory_PiecewiseC1
-- name    : ResetInventory_PiecewiseC1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:40.314017+00:00
-- url     : https://prove2.me/theorems/e6c65c8c-1a93-4def-bc0b-d6f05db22dba
-- title:
--   Assumption T without its Lipschitz requirement: piecewise $C^1$ on $[0,c_{\max}]$
-- statement:
--   A function $V$ (in the mission, $V=J(\cdot,t+1)$) is **piecewise $C^1$ on $[0,c_{\max}]$ with derivative bound $M\ge0$** if there is a partition
--   $$
--   0=z_0<z_1<\dots<z_n=c_{\max}
--   $$
--   such that on each closed piece $Z_i=[z_{i-1},z_i]$ the function $V$ has a derivative (one-sided at $z_{i-1}$ and $z_i$) that is continuous on $Z_i$ and bounded in absolute value by $M$.
--
--   This is Assumption T of the paper (for a fixed $t$, $J(z,t+1)=J_i(z,t+1)$ on $Z_{i,t}$, with each $\partial_zJ_i$ bounded by $M_{t+1}$), except that the paper also asks each $\partial_zJ_i$ to be Lipschitz. Since adjacent pieces share endpoints, $V$ is continuous on $[0,c_{\max}]$, which is how the paper reads AT ("AT assumes that the value function is continuous and piecewise differentiable", p.17).
--
--   **Formalization Note** The piece $J_i$ is $V$ restricted to $Z_i$, so the condition is stated on $V$ itself. The Lipschitz requirement is dropped: the proofs use only the continuity of the pieces and their derivatives and the bound $M$, and the requirement fails in general for the value functions of Theorem 1 (see the correction recorded there). When $c_{\max}=0$ the partition is the single point $z_0=0$.
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Assumption T, (26)–(27), p.17; proof of Proposition 2, p.30

import Mathlib

namespace ResetInventory

/-- **Assumption T (AT)** of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, p.17, for one
function `V = J(·, t + 1)`, without its Lipschitz requirement: there is a partition
`0 = z₀ < z₁ < ⋯ < z_n = c_max` of `[0, c_max]` (27) such that on each closed piece
`Z_i = [z_{i-1}, z_i]` the function `V` coincides with a piece `J_i` (26) whose derivative is
continuous and absolutely bounded by the finite non-negative constant `M` (= `M_{t+1}`).

**Formalization Note** The piece `J_i` is `V` restricted to `Z_i`, so the condition is stated on
`V` itself: `V` has a derivative within `Z_i` at every point of `Z_i` (one-sided at the two
endpoints), that derivative is continuous on `Z_i`, and its absolute value is at most `M`. Because
neighbouring closed pieces share their endpoint, `V` is continuous on `[0, c_max]`, which is the
paper's reading of AT ("AT assumes that the value function is continuous and piecewise
differentiable", p.17). The paper also asks the derivative of each piece to be Lipschitz; that
requirement is dropped here (the proofs use only continuity and the bound `M`, and the requirement
fails for the value functions of Theorem 1 in general, see the correction recorded with
Theorem 1). When `c_max = 0` the partition is the single point `z₀ = 0` (`n = 0`). -/
def PiecewiseC1 (cmax M : ℝ) (V : ℝ → ℝ) : Prop :=
  0 ≤ M ∧
  ∃ (n : ℕ) (z : ℕ → ℝ), z 0 = 0 ∧ z n = cmax ∧ (∀ i < n, z i < z (i + 1)) ∧
    ∀ i < n, ∃ V' : ℝ → ℝ, ContinuousOn V' (Set.Icc (z i) (z (i + 1))) ∧
      ∀ y ∈ Set.Icc (z i) (z (i + 1)),
        HasDerivWithinAt V (V' y) (Set.Icc (z i) (z (i + 1))) y ∧ |V' y| ≤ M

end ResetInventory


