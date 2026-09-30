-- Prove2me | Definitions.Def_BorkarMeynODE_Tapering_FlowsOnBlocks
-- name    : BorkarMeynODE_Tapering_FlowsOnBlocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:40:32.65256+00:00
-- url     : https://prove2.me/theorems/a73fec5d-2f55-44be-ab72-72234c3b293b
-- title:
--   Piecewise ODE solutions $\hat\phi$ (scaled ODE) and $\phi^\infty$ (fluid limit), restarted on each block
-- statement:
--   Keep the notation of the scaled interpolation: step sizes $a$, block length $T>0$, block times $T(j)$, block scales $r(j)$, and the scaled interpolated process $\phi$ of a sample path. A function $\hat\phi:[0,\infty)\to\mathbb R^d$ is the **piecewise solution of the scaled ODE** if for every $j\ge0$ it solves
--   $$
--   \dot x(t) = h_{r(j)}\big(x(t)\big), \qquad t\in[T(j),T(j+1)), \tag{4.1}
--   $$
--   with the initial condition $\hat\phi(T(j)) = \phi(T(j))$. Likewise $\phi^\infty$ is the **piecewise solution of the fluid limit** if on every block it solves $\dot x(t) = h_\infty(x(t))$ with $\phi^\infty(T(j)) = \phi(T(j))$.
--
--   Both are restarted at the start of each block from the current rescaled iterate. They are the deterministic comparison curves of Section 4.1: $\hat\phi$ tracks $\phi$ (Lemma 4.6) and is close to $\phi^\infty$ for large scales (Lemma 4.4).
--
--   **Formalization Note** The functions are characterized by a predicate rather than constructed: on each block the derivative is taken within $[T(j),T(j+1))$ (two-sided in the interior, one-sided at $T(j)$), so the curve is continuous on each block. Because $h_{r}$ and $h_\infty$ are Lipschitz under (A1), forward solutions exist and are unique, so the predicate determines $\hat\phi$ and $\phi^\infty$ on $[0,\infty)$ whenever the blocks cover $[0,\infty)$ (under (TS) or (BS)). Theorems quantify over every function satisfying it.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 461, items (b) and (c), Eq. (4.1)

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_AssumptionA1
import Definitions.Def_BorkarMeynODE_Tapering_TimeGrid
import Definitions.Def_BorkarMeynODE_Tapering_ScaledInterpolation

namespace BorkarMeynODE.Tapering

/-- `φh` is the paper's `φ̂` along the sample path `x` (p. 461, (b)): on every block
`[T(j), T(j+1))` it solves (4.1) `ẋ = h_{r(j)}(x)` (derivative within the block: two-sided in
the interior, from the right at `T(j)`), with initial condition `φ̂(T(j)) = φ(T(j))`. Since
`h_{r(j)}` is Lipschitz, forward solutions exist and are unique, so this predicate determines
`φh` on `[0, ∞)` whenever the blocks cover `[0, ∞)`. -/
def IsScaledFlowOnBlocks {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (a : ℕ → ℝ) (T : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (φh : ℝ → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∀ j : ℕ, φh (blockTime a T j) = phi a T x (blockTime a T j) ∧
    ∀ t ∈ Set.Ico (blockTime a T j) (blockTime a T (j + 1)),
      HasDerivWithinAt φh (scaledField h (blockScale a T x j) (φh t))
        (Set.Ico (blockTime a T j) (blockTime a T (j + 1))) t

/-- `φi` is the paper's `φ^∞` along the sample path `x` (p. 461, (c)): on every block
`[T(j), T(j+1))` it solves the fluid-limit ODE (1.5) `ẋ = h_∞(x)`, with initial condition
`φ^∞(T(j)) = φ(T(j))`. -/
def IsFluidFlowOnBlocks {d : ℕ} (hInf : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (a : ℕ → ℝ) (T : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d)) (φi : ℝ → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∀ j : ℕ, φi (blockTime a T j) = phi a T x (blockTime a T j) ∧
    ∀ t ∈ Set.Ico (blockTime a T j) (blockTime a T (j + 1)),
      HasDerivWithinAt φi (hInf (φi t))
        (Set.Ico (blockTime a T j) (blockTime a T (j + 1))) t

end BorkarMeynODE.Tapering


