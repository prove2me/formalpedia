-- Prove2me | Definitions.Def_BilinearGramian_Integrability_Example33
-- name    : BilinearGramian_Integrability_Example33
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:19.202125+00:00
-- url     : https://prove2.me/theorems/2b16f299-6013-4e79-a973-a9c7898698f2
-- title:
--   The data of Example 3.3: A = diag(−1, −2), N = ν[0 1; 1 0], b = (1, 1)ᵀ
-- statement:
--   Example 3.3 of the paper is a single-input ($m = 1$) bilinear system in the plane ($n = 2$),
--   $$\dot x = Ax + N x\,u + b\,u,$$
--   with
--   $$A = \begin{bmatrix} -1 & 0 \\ 0 & -2 \end{bmatrix}, \qquad N = \nu \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}, \qquad b = \begin{bmatrix} 1 \\ 1 \end{bmatrix},$$
--   where $\nu$ is a real parameter. The matrix $A$ is stable (eigenvalues $-1$ and $-2$), so the Lyapunov equation (3.9) has a unique solution $\tilde P(x)$ for every state $x$.
--
--   These matrices are the whole input of the counterexample to the gradient formula (3.8).
--
--   **Formalization Note** `exA`, `exN ν` and `exb` are the three matrices above; `exB` is `b` viewed as the $2 \times 1$ input matrix $B = [b]$, so that the general (3.9) of the companion definition file applies with $m = 1$ and $N_1 = N$.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 698, Example 3.3

import Mathlib

open Matrix

namespace BilinearGramian.Integrability

/-- The drift matrix of Example 3.3 (Benner–Damm 2011, p. 698): `A = diag(-1, -2)`. -/
def exA : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, -2]

/-- The bilinear coupling matrix of Example 3.3 (p. 698): `N = ν [0 1; 1 0]`, with a real
parameter `ν`. The example has a single input, `m = 1`. -/
def exN (ν : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := ν • !![0, 1; 1, 0]

/-- The input vector of Example 3.3 (p. 698): `b = (1, 1)ᵀ`. -/
def exb : Fin 2 → ℝ := ![1, 1]

/-- `b` as the `2 × 1` input matrix `B = [b]` of the single-input system (`m = 1`). -/
def exB : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => exb i

end BilinearGramian.Integrability


