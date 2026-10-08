-- Prove2me | Definitions.Def_SelfDualLP_Output_Neighborhood
-- name    : SelfDualLP_Output_Neighborhood
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:25:32.819976+00:00
-- url     : https://prove2.me/theorems/cf8ddaa6-c8a8-43d5-ae29-e704cab085fb
-- title:
--   The null space Q, the gap μ and the central-path neighborhood N(β) of (HLP)
-- statement:
--   Work with the data of (HLP) under the choice (7) ($y^0=0$, $x^0=s^0=e$). This file defines three objects.
--
--   1. **The null space $Q$.** A direction $(d_y,d_x,d_\tau,d_\theta,d_s,d_\kappa)$ is in $Q$ if
--   $$
--   \begin{aligned}
--   A d_x - b d_\tau + \bar b d_\theta &= 0,\\
--   -A^Td_y + c d_\tau - \bar c d_\theta - d_s &= 0,\\
--   b^Td_y - c^Td_x + \bar z d_\theta - d_\kappa &= 0,\\
--   -\bar b^Td_y + \bar c^Td_x - \bar z d_\tau &= 0,
--   \end{aligned}
--   $$
--   i.e. it lies in the null space of the constraint matrix of (HLP) after the surplus variables $s,\kappa$ are added.
--   2. **The gap and $\mu$.** For a point $(y,x,\tau,\theta,s,\kappa)$, the gap is $x^Ts+\tau\kappa$ and $\mu=(x^Ts+\tau\kappa)/(n+1)$.
--   3. **The neighborhood.** For $\beta\in(0,1)$,
--   $$
--   \mathcal N(\beta)=\left\{(y,x,\tau,\theta,s,\kappa)\in\mathcal F_h^0 : \left\|\begin{pmatrix}Xs\\ \tau\kappa\end{pmatrix}-\mu e\right\|\le\beta\mu\right\},
--   $$
--   where $X=\operatorname{diag}(x)$ and $\|\cdot\|$ is the Euclidean norm on $\mathbb R^{n+1}$.
--
--   The predictor–corrector algorithm keeps its iterates in $\mathcal N(1/4)$ after corrector steps and in $\mathcal N(1/2)$ after predictor steps.
--
--   **Formalization Note** The norm is written out as $\sqrt{\sum_j (x_js_j-\mu)^2+(\tau\kappa-\mu)^2}$, because Lean's norm on $\mathbb R^n$-valued functions is the sup norm.
-- source:
--   Ye, Todd, Mizuno, An O(√nL)-Iteration Homogeneous and Self-Dual Linear Programming Algorithm, Math. Oper. Res. 19(1) (1994), p. 59, Theorem 5 (ii) (the null space Q); p. 60, N(β); DOI 10.1287/moor.19.1.53

import Mathlib
import Definitions.Def_SelfDualLP_Output_HLP

open Matrix

namespace SelfDualLP.Output

/-- `d ∈ Q`: the direction `d = (d_y, d_x, d_τ, d_θ, d_s, d_κ)` lies in the null space of the
constraint matrix of (HLP) after adding the surplus variables `s` and `κ`
(Theorem 5 (ii), p. 59):
`A d_x − b d_τ + b̄ d_θ = 0`, `−Aᵀd_y + c d_τ − c̄ d_θ − d_s = 0`,
`bᵀd_y − cᵀd_x + z̄ d_θ − d_κ = 0`, `−b̄ᵀd_y + c̄ᵀd_x − z̄ d_τ = 0`,
with `b̄, c̄, z̄` built from `(x⁰, y⁰, s⁰)` by (5). -/
def InQ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (d : HLPPoint m n) : Prop :=
  A *ᵥ d.x - d.τ • b + d.θ • bbar A b x0 = 0 ∧
  -(Aᵀ *ᵥ d.y) + d.τ • c - d.θ • cbar A c y0 s0 - d.s = 0 ∧
  b ⬝ᵥ d.y - c ⬝ᵥ d.x + zbar b c x0 y0 * d.θ - d.κ = 0 ∧
  -(bbar A b x0 ⬝ᵥ d.y) + cbar A c y0 s0 ⬝ᵥ d.x - zbar b c x0 y0 * d.τ = 0

/-- `Q` under the choice (7) `y⁰ = 0, x⁰ = s⁰ = e`. -/
def InQ7 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (d : HLPPoint m n) : Prop :=
  InQ A b c (ones n) 0 (ones n) d

/-- The complementarity gap `xᵀs + τκ`. -/
def gap {m n : ℕ} (z : HLPPoint m n) : ℝ :=
  z.x ⬝ᵥ z.s + z.τ * z.κ

/-- `μ = (xᵀs + τκ)/(n + 1)`. -/
noncomputable def mu {m n : ℕ} (z : HLPPoint m n) : ℝ :=
  gap z / ((n : ℝ) + 1)

/-- `‖(Xs; τκ) − μe‖`, the Euclidean (ℓ₂) norm in `ℝ^{n+1}` of the deviation of the vector
`(x₁s₁, …, xₙsₙ, τκ)` from `μ e`. -/
noncomputable def centralityDeviation {m n : ℕ} (z : HLPPoint m n) : ℝ :=
  Real.sqrt ((∑ j, (z.x j * z.s j - mu z) ^ 2) + (z.τ * z.κ - mu z) ^ 2)

/-- The neighborhood `𝒩(β) = {z ∈ 𝓕_h° : ‖(Xs; τκ) − μe‖ ≤ βμ}` of the central path of (HLP)
under (7) (p. 60). -/
def Nbhd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (β : ℝ)
    (z : HLPPoint m n) : Prop :=
  HLPStrictlyFeasible7 A b c z ∧ centralityDeviation z ≤ β * mu z

end SelfDualLP.Output


