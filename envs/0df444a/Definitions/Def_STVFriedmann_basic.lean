-- Prove2me | Definitions.Def_STVFriedmann_basic
-- name    : STVFriedmann_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T01:54:59.516347+00:00
-- url     : https://prove2.me/theorems/53f9bf0b-cf6c-40e5-b538-5a1a0960fbca
-- title:
--   STV ODE of orders 1 and 2, rest points, block $P_k$, and the $k=-1$ Friedmann curve
-- statement:
--   This file defines the objects used throughout the mission, following Sections 2.3–2.7 of Alexander–Temple–Vogler (arXiv:2510.14228).
--
--   1. **The STV ODE of order 1** (`stvField1`), eqs. (2.34)–(2.35). This is the vector field $F_1:\mathbb R^2\to\mathbb R^2$ in the coordinates $(z_2,w_0)$:
--   $$F_1(z_2,w_0)=\left(2z_2-3z_2w_0,\;-\tfrac16z_2+w_0-w_0^2\right).$$
--   2. **The STV ODE of order 2** (`stvField2`), eqs. (2.48)–(2.51). This is the vector field $F_2:\mathbb R^4\to\mathbb R^4$ in the coordinates $(z_2,w_0,z_4,w_2)$:
--   $$F_2=\left(2z_2-3z_2w_0,\;-\tfrac16z_2+w_0-w_0^2,\;\tfrac5{12}z_2^2w_0+4z_4-5w_0z_4-5z_2w_2,\;-\tfrac1{24}z_2^2+\tfrac14z_2w_0^2-\tfrac1{10}z_4+3w_2-4w_0w_2\right).$$
--   3. **Solutions** (`IsSTVSolution F U`). The STV ODE $\bar t\,\dot U=F(U)$ is autonomous in log-time $\tau=\ln\bar t$. A solution for all $\bar t\in(0,\infty)$ is a differentiable map $U:\mathbb R\to\mathbb R^{m}$ with $U'(\tau)=F(U(\tau))$ for every $\tau\in\mathbb R$. The Big Bang $\bar t\to0^+$ corresponds to $\tau\to-\infty$.
--   4. **Rest points** (2.27). The unstable point $U=(0,0)$, the Minkowski point $M=(0,1)$ and the critical Friedmann point $SM=(\tfrac43,\tfrac23)$ at order 1. At order 2 these are $U=(0,0,0,0)$, $M=(0,1,0,0)$ and $SM=(\tfrac43,\tfrac23,\tfrac{40}{27},\tfrac29)$.
--   5. **The block $P_k$** (`stvBlockP k v`), eq. (2.26). For $\boldsymbol v_1=(z_2,w_0)$,
--   $$P_k(\boldsymbol v_1)=\begin{pmatrix}(2k+1)(1-w_0)-1&-(2k+1)z_2\\-\frac1{2(2k+1)}&2k(1-w_0)-1\end{pmatrix}.$$
--   6. **The $k=-1$ Friedmann curve** (Theorem 5). The normalized time is `bigBangTime` $\theta\mapsto\tfrac12(\sinh2\theta-2\theta)$, so that $\bar t=\Delta_0\cdot\tfrac12(\sinh2\theta-2\theta)$. The coefficients are
--   $$\tilde z_2=\frac{6(\sinh2\theta-2\theta)^2}{(\cosh2\theta-1)^3},\quad \tilde w_0=\frac{(\sinh2\theta-2\theta)\sinh2\theta}{(\cosh2\theta-1)^2},$$
--   $$\tilde z_4=\frac{30(\sinh2\theta-2\theta)^4\cosh^2\theta}{(\cosh2\theta-1)^6},\quad \tilde w_2=\frac{3(\sinh2\theta-2\theta)^3\cosh\theta}{2(\cosh2\theta-1)^4\sinh\theta}.$$
--   They are collected into `friedmannCurve1` $=(\tilde z_2,\tilde w_0)$ and `friedmannCurve2` $=(\tilde z_2,\tilde w_0,\tilde z_4,\tilde w_2)$.
--
--   These definitions put the paper's dynamical-systems statements in one shared vocabulary. The goal theorem and every milestone of the mission are stated in terms of them.
--
--   **Formalization Note** Points of phase space are `Fin 2 → ℝ` or `Fin 4 → ℝ`, with indices $0,1,2,3$ standing for $z_2,w_0,z_4,w_2$. The Friedmann coefficients are only meaningful for $\theta>0$; the theorems use them only there.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, pp. 11-17, eqs. (2.26), (2.27), (2.34)-(2.35), (2.40)-(2.43), (2.48)-(2.51)

import Mathlib

/-!
# The STV ODE for pressureless (p = 0) Friedmann spacetimes — basic definitions

Source: C. Alexander, B. Temple, Z. Vogler, *The instability of the critical Friedmann
spacetime at the Big Bang as an alternative to dark energy*, arXiv:2510.14228v1 (2025),
Section 2.3–2.7, equations (2.26), (2.27), (2.34)–(2.35), (2.40)–(2.43), (2.48)–(2.51).

Conventions.
* Points of the order-`n` STV phase space are vectors `Fin (2n) → ℝ`.  For `n = 1` the
  coordinates are `(z₂, w₀)`; for `n = 2` they are `(z₂, w₀, z₄, w₂)` (indices `0,1,2,3`).
* The STV ODE `t̄ U̇ = F(U)` is autonomous in log-time `τ = ln t̄` (paper, Section 2.4):
  `dU/dτ = F(U)`.  A solution on the whole time axis `t̄ ∈ (0, ∞)` is therefore a
  function `U : ℝ → Fin (2n) → ℝ` of `τ ∈ ℝ`; `τ → -∞` is the Big Bang `t̄ → 0⁺` and
  `τ → +∞` is `t̄ → ∞`.
-/

namespace STVFriedmann

open Real

/-- The STV ODE of order `n = 1`, equations (2.34)–(2.35), in coordinates `(z₂, w₀)`:
`t̄ ż₂ = 2 z₂ − 3 z₂ w₀`, `t̄ ẇ₀ = −z₂/6 + w₀ − w₀²`. -/
noncomputable def stvField1 (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![2 * u 0 - 3 * u 0 * u 1,
    -(1 / 6) * u 0 + u 1 - u 1 ^ 2]

/-- The STV ODE of order `n = 2`, equations (2.48)–(2.51), in coordinates
`(z₂, w₀, z₄, w₂)`. -/
noncomputable def stvField2 (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![2 * u 0 - 3 * u 0 * u 1,
    -(1 / 6) * u 0 + u 1 - u 1 ^ 2,
    (5 / 12) * u 0 ^ 2 * u 1 + 4 * u 2 - 5 * u 1 * u 2 - 5 * u 0 * u 3,
    -(1 / 24) * u 0 ^ 2 + (1 / 4) * u 0 * u 1 ^ 2 - (1 / 10) * u 2 + 3 * u 3
      - 4 * u 1 * u 3]

/-- `U` is a solution of the autonomous system `dU/dτ = F(U)` for all log-times
`τ = ln t̄ ∈ ℝ`, i.e. a solution of `t̄ U̇ = F(U)` for all `t̄ > 0`. -/
def IsSTVSolution {m : ℕ} (F : (Fin m → ℝ) → Fin m → ℝ) (U : ℝ → Fin m → ℝ) : Prop :=
  ∀ τ : ℝ, HasDerivAt U (F (U τ)) τ

/-- The unstable rest point `U = (0, 0)` of the order-1 system. -/
def restU1 : Fin 2 → ℝ := ![0, 0]
/-- The Minkowski rest point `M = (0, 1)` of the order-1 system, (2.27). -/
def restM1 : Fin 2 → ℝ := ![0, 1]
/-- The critical (`k = 0`) Friedmann rest point `SM = (4/3, 2/3)` of the order-1 system,
(2.27). -/
noncomputable def restSM1 : Fin 2 → ℝ := ![4 / 3, 2 / 3]

/-- The unstable rest point `U = (0, 0, 0, 0)` of the order-2 system. -/
def restU2 : Fin 4 → ℝ := ![0, 0, 0, 0]
/-- The Minkowski rest point `M = (0, 1, 0, 0)` of the order-2 system, (2.27). -/
def restM2 : Fin 4 → ℝ := ![0, 1, 0, 0]
/-- The critical (`k = 0`) Friedmann rest point `SM = (4/3, 2/3, 40/27, 2/9)` of the
order-2 system, (2.27). -/
noncomputable def restSM2 : Fin 4 → ℝ := ![4 / 3, 2 / 3, 40 / 27, 2 / 9]

/-- The `2 × 2` matrix `P_k(v₁)` of (2.26), for `v₁ = (z₂, w₀)`:
`P_k = [[(2k+1)(1−w₀) − 1, −(2k+1) z₂], [−1/(2(2k+1)), 2k(1−w₀) − 1]]`. -/
noncomputable def stvBlockP (k : ℕ) (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(2 * k + 1) * (1 - v 1) - 1, -((2 * k + 1) * v 0);
     -(1 / (2 * (2 * k + 1))), 2 * k * (1 - v 1) - 1]

/-- The normalized comoving time of the `p = 0`, `k = −1` Friedmann spacetime as a
function of the development angle `θ` (Theorem 5): `t / Δ₀ = (sinh 2θ − 2θ)/2`. -/
noncomputable def bigBangTime (θ : ℝ) : ℝ := (sinh (2 * θ) - 2 * θ) / 2

/-- `z̃₂(θ) = 6 (sinh 2θ − 2θ)² / (cosh 2θ − 1)³`, equation (2.41). -/
noncomputable def friedmannZ2 (θ : ℝ) : ℝ :=
  6 * (sinh (2 * θ) - 2 * θ) ^ 2 / (cosh (2 * θ) - 1) ^ 3

/-- `w̃₀(θ) = (sinh 2θ − 2θ) sinh 2θ / (cosh 2θ − 1)²`, equation (2.41). -/
noncomputable def friedmannW0 (θ : ℝ) : ℝ :=
  (sinh (2 * θ) - 2 * θ) * sinh (2 * θ) / (cosh (2 * θ) - 1) ^ 2

/-- `z̃₄(θ) = 30 (sinh 2θ − 2θ)⁴ cosh² θ / (cosh 2θ − 1)⁶`, equation (2.43). -/
noncomputable def friedmannZ4 (θ : ℝ) : ℝ :=
  30 * (sinh (2 * θ) - 2 * θ) ^ 4 * cosh θ ^ 2 / (cosh (2 * θ) - 1) ^ 6

/-- `w̃₂(θ) = 3 (sinh 2θ − 2θ)³ cosh θ / (2 (cosh 2θ − 1)⁴ sinh θ)`, equation (2.43). -/
noncomputable def friedmannW2 (θ : ℝ) : ℝ :=
  3 * (sinh (2 * θ) - 2 * θ) ^ 3 * cosh θ / (2 * (cosh (2 * θ) - 1) ^ 4 * sinh θ)

/-- The leading-order (`n = 1`) projection `(z̃₂(θ), w̃₀(θ))` of the `k = −1` Friedmann
spacetime, (2.40)–(2.41). -/
noncomputable def friedmannCurve1 (θ : ℝ) : Fin 2 → ℝ := ![friedmannZ2 θ, friedmannW0 θ]

/-- The order-2 projection `(z̃₂, w̃₀, z̃₄, w̃₂)(θ)` of the `k = −1` Friedmann spacetime,
(2.41) and (2.43). -/
noncomputable def friedmannCurve2 (θ : ℝ) : Fin 4 → ℝ :=
  ![friedmannZ2 θ, friedmannW0 θ, friedmannZ4 θ, friedmannW2 θ]

end STVFriedmann


