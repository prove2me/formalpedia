-- Prove2me | Definitions.Def_SuttonBartoRL_Traces_DutchMC
-- name    : SuttonBartoRL_Traces_DutchMC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:17:12.577125+00:00
-- url     : https://prove2.me/theorems/1af937ed-15da-4aed-91b0-d232562ef2e3
-- title:
--   Linear Monte Carlo (LMS) weights, fading matrices $F_t = I - \alpha x_t x_t^\top$, the dutch trace and the auxiliary vector
-- statement:
--   Fix a dimension $d$, a step size $\alpha \in \mathbb R$, a final return $G \in \mathbb R$, an initial weight vector $w_0 \in \mathbb R^d$, and the feature vectors $x_0, x_1, \dots \in \mathbb R^d$ observed at the time steps of one episode of length $T$.
--
--   1. The **fading matrix** at time $t$ is $F_t = I - \alpha x_t x_t^\top$, and for indices $j, t$ the ordered product $F_t F_{t-1} \cdots F_j$ (latest factor on the left) is the identity when $t < j$.
--   2. The **forward view** is the linear gradient Monte Carlo, or LMS, algorithm (12.13): starting from $w_0$,
--   $$
--   w_{t+1} = w_t + \alpha\,[G - w_t^\top x_t]\,x_t, \qquad 0 \le t < T.
--   $$
--   The same return $G$ (a single reward at the end of the episode, no discounting) is used at every step.
--   3. The **dutch trace** is computed step by step without $G$: $z_0 = x_0$ and
--   $$
--   z_t = z_{t-1} + (1 - \alpha z_{t-1}^\top x_t)\,x_t, \qquad t \ge 1 .
--   $$
--   4. The **auxiliary vector** is computed step by step without $G$ by $a_t = a_{t-1} - \alpha x_t x_t^\top a_{t-1}$, started from $a_{-1} = w_0$, so that $a_0 = w_0 - \alpha x_0 x_0^\top w_0 = F_0 w_0$.
--
--   These are the forward-view and backward-view algorithms of §12.6. The backward view takes $O(d)$ time and memory per step and never stores past feature vectors.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` and matrices `Matrix (Fin d) (Fin d) ℝ`; $x x^\top$ is `Matrix.vecMulVec x x`. The features are a sequence indexed by $\mathbb N$, and only $x_0, \dots, x_{T-1}$ enter the quantities at times up to $T - 1$ (resp. $w_T$). The initialization $a_0 = F_0 w_0$ is a **correction**. The book prints $a_0 = w_0$, which contradicts its own definition $a_t \doteq F_t F_{t-1}\cdots F_0 w_0$ at $t = 0$ and breaks (12.14). For example, with $d = 1$, $T = 1$, $x_0 = 1$, $\alpha = 1/2$, $w_0 = 1$, $G = 0$, the forward view gives $w_1 = 1/2$ but $a_0 + \alpha G z_0 = 1$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §12.6 *Dutch Traces in Monte Carlo Learning*, Eq. (12.13), p. 301, and the fading matrix, dutch trace and auxiliary vector a_t, p. 302 (a_0 corrected to F_0 w_0)

import Mathlib

namespace SuttonBartoRL.Traces

open Matrix

variable {d : ℕ}

/-- The forgetting (fading) matrix `F_t ≐ I − α x_t x_tᵀ` of Sutton & Barto, §12.6, p. 302,
for a step size `α` and the feature vectors `x_0, x_1, … ∈ ℝ^d` of one episode. -/
def fadingMatrix (α : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  1 - α • Matrix.vecMulVec (x t) (x t)

/-- The ordered product `F_t F_{t−1} ⋯ F_j` of fading matrices (latest factor on the left).
It is the identity matrix when `t < j` (empty product); for example `fadeProd α x (k + 1) t`
is `F_t F_{t−1} ⋯ F_{k+1}` and equals `I` at `k = t`, and `fadeProd α x 0 t` is `F_t ⋯ F_0`. -/
def fadeProd (α : ℝ) (x : ℕ → Fin d → ℝ) (j : ℕ) : ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => if j = 0 then fadingMatrix α x 0 else 1
  | t + 1 => if j ≤ t + 1 then fadingMatrix α x (t + 1) * fadeProd α x j t else 1

/-- The forward view: the linear gradient Monte Carlo (LMS) weights (12.13),
`w_0` given and `w_{t+1} ≐ w_t + α [G − w_tᵀ x_t] x_t`, with one final return `G` shared
by every step and no discounting (p. 301). Only `x_0, …, x_{T−1}` enter `w_T`. -/
def lmsWeights (α G : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) : ℕ → Fin d → ℝ
  | 0 => w₀
  | t + 1 => lmsWeights α G x w₀ t + (α * (G - lmsWeights α G x w₀ t ⬝ᵥ x t)) • x t

/-- The dutch trace for `γλ = 1` (p. 302), computed incrementally and without `G`:
`z_0 = x_0` and `z_t = z_{t−1} + (1 − α z_{t−1}ᵀ x_t) x_t` for `t ≥ 1`. -/
def dutchTrace (α : ℝ) (x : ℕ → Fin d → ℝ) : ℕ → Fin d → ℝ
  | 0 => x 0
  | t + 1 => dutchTrace α x t + (1 - α * (dutchTrace α x t ⬝ᵥ x (t + 1))) • x (t + 1)

/-- The auxiliary memory vector `a_t` of p. 302, computed incrementally by
`a_t = a_{t−1} − α x_t x_tᵀ a_{t−1}`, started from `a_{−1} = w_0`, i.e.
`a_0 = w_0 − α x_0 x_0ᵀ w_0 = F_0 w_0`. This is the **corrected** initialization: the book
prints `a_0 = w_0`, which contradicts its own definition `a_t ≐ F_t F_{t−1} ⋯ F_0 w_0` at `t = 0`. -/
def auxVec (α : ℝ) (x : ℕ → Fin d → ℝ) (w₀ : Fin d → ℝ) : ℕ → Fin d → ℝ
  | 0 => w₀ - (α * (x 0 ⬝ᵥ w₀)) • x 0
  | t + 1 => auxVec α x w₀ t - (α * (x (t + 1) ⬝ᵥ auxVec α x w₀ t)) • x (t + 1)

end SuttonBartoRL.Traces


