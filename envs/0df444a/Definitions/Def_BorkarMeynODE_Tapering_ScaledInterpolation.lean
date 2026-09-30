-- Prove2me | Definitions.Def_BorkarMeynODE_Tapering_ScaledInterpolation
-- name    : BorkarMeynODE_Tapering_ScaledInterpolation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:39:34.299991+00:00
-- url     : https://prove2.me/theorems/3e1b9f4c-5348-4643-a469-440bc2233aec
-- title:
--   Scaled interpolated process $\phi$: block scale $r(j)$ and block functions $\phi_j$
-- statement:
--   Fix step sizes $\{a(n)\}$, a block length $T>0$, and a sample path $\{X(n)\}$ of the recursion, with time grid $t(n)$ and blocks $T(j)=t(m(j))$. The **scale of block $j$** is
--   $$
--   r(j) = \max\big(1, \|X(m(j))\|\big), \qquad j\ge0 .
--   $$
--   The **block function** $\phi_j$ on $[T(j),T(j+1)]$ is the piecewise-linear function with
--   $$
--   \phi_j\big(t(n)\big) = \frac{X(n)}{r(j)}, \qquad m(j)\le n\le m(j+1),
--   $$
--   linearly interpolated in between, and the **scaled interpolated process** is
--   $$
--   \phi(t) = \phi_j(t), \qquad t\in[T(j),T(j+1)),\ j\ge0 .
--   $$
--   Thus on each block the iterates are rescaled by their size at the start of the block, and $\phi$ has jumps at the block boundaries: $\phi_j(T(j+1)) = X(m(j+1))/r(j)$ is the left limit $\phi(T(j+1)-)$, while $\phi(T(j+1)) = X(m(j+1))/r(j+1)$.
--
--   The process $\phi$ is the object that is compared with solutions of the scaled ODE (1.4) in Lemmas 4.5 and 4.6.
--
--   **Formalization Note** The objects are defined for a deterministic sequence `x : ℕ → ℝ^d`; statements about the random iterates apply them to each sample path `fun n => X n ω`.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 460, definition of r(j), phi_j and phi (item (a))

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_TimeGrid

namespace BorkarMeynODE.Tapering

/-- The scale of block `j` along a sample path `x = (X(n))_n` (p. 460):
`r(j) = max(1, ‖X(m(j))‖)`. -/
noncomputable def blockScale {d : ℕ} (a : ℕ → ℝ) (T : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (j : ℕ) : ℝ :=
  max 1 ‖x (blockIndex a T j)‖

/-- The block function `φ_j` on the closed interval `[T(j), T(j+1)]` (p. 460, (a)):
`φ_j(t(n)) = X(n)/r(j)` for `m(j) ≤ n ≤ m(j+1)`, linearly interpolated in between. In
particular `φ_j(T(j+1)) = X(m(j+1))/r(j)`, the paper's `φ(T(j+1)−)`. -/
noncomputable def phiBlock {d : ℕ} (a : ℕ → ℝ) (T : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (j : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  gridInterp a (fun n => (blockScale a T x j)⁻¹ • x n) t

/-- The scaled interpolated process `φ` (p. 460): `φ(t) = φ_j(t)` for `t ∈ [T(j), T(j+1))`. -/
noncomputable def phi {d : ℕ} (a : ℕ → ℝ) (T : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  phiBlock a T x (blockOfTime a T t) t

end BorkarMeynODE.Tapering


