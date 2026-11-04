-- Prove2me | Definitions.Def_StochHiddenConvex_Model_GlobalModel
-- name    : StochHiddenConvex_Model_GlobalModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:09.567206+00:00
-- url     : https://prove2.me/theorems/2c0235bd-c3a3-48ee-bd91-5568dc2e7683
-- title:
--   The global model: Assumptions 2.1(b), 2.2(c), 2.3(a),(c) on all of $\mathbb R^d$
-- statement:
--   The proof of Theorem 3.2 evaluates $g$ at the points $x^t-\gamma v_F(x^t)$, which leave the box $\mathcal X$. The run-level displays of that proof are stated with the following conditions, each a separate predicate:
--
--   1. **MonotoneGlobal.** For almost every $\xi$, every $\phi_i(\cdot,\xi_i)$ is non-decreasing on all of $\mathbb R$ (Assumption 2.1(b) without a domain restriction; used in Lemma 3.1).
--   2. **IntegrableGlobal.** $g_i(y)=\mathbb E\phi_i(y,\xi_i)$ exists for every $y\in\mathbb R$.
--   3. **LipschitzGlobal.** For almost every $\xi$, $\|\phi(x,\xi)-\phi(y,\xi)\|\le L_\phi\|x-y\|$ for all $x,y\in\mathbb R^d$ (used for (26)).
--   4. **SmoothGlobal.** Every $g_i$ is differentiable on $\mathbb R$ and $|g_i'(x_i)-g_i'(y_i)|\le S_g\|x-y\|$ for all $x,y\in\mathbb R^d$ (Assumption 2.3(a),(c) on $\mathbb R^d$; used for the Taylor step (29)).
--
--   `GlobalModel` is the conjunction of 1, 3 and 4. The paper's applications (e.g. $\phi(x,\xi)=x\wedge\xi$ with a Lipschitz distribution function) satisfy these conditions, while Assumption 2.3(b) holds only on $\mathcal X$ there, and stays on $\mathcal X$.
-- source:
--   X. Chen, N. He, Y. Hu, Z. Ye, Efficient Algorithms for A Class of Stochastic Hidden Convex Optimization and Its Applications in Network Revenue Management, arXiv:2205.01774v3, Appendix C, pp.38–40; Lemma 3.1 proof, p.32; Assumptions 2.1(b), 2.2(c), 2.3, pp.8–10

import Mathlib
import Definitions.Def_StochHiddenConvex_Model

open MeasureTheory

namespace StochHiddenConvex

namespace Model

variable {d : ℕ} (M : Model d)

/-- Assumption 2.1(b) on all of `ℝ` (Chen, He, Hu & Ye, arXiv:2205.01774v3, p.8, and its use in
the proof of Lemma 3.1, p.32): for `ℙ`-almost every `ξ`, every `ϕᵢ(·, ξᵢ)` is non-decreasing on
`ℝ`. -/
def MonotoneGlobal : Prop := ∀ᵐ s ∂M.P, ∀ i, Monotone (fun y => M.phi i y (s i))

/-- The expectation `gᵢ(y) = 𝔼ϕᵢ(y, ξᵢ)` exists at every `y ∈ ℝ` (arXiv:2205.01774v3, (3), p.8,
used at points outside `𝒳` in Lemma 3.1, p.32). -/
def IntegrableGlobal : Prop := ∀ (x : Vec d) (i : Fin d), Integrable (fun s => M.phi i (x i) (s i)) M.P

/-- Assumption 2.2(c) on all of `ℝ^d` (arXiv:2205.01774v3, p.9, and its use on p.39 "g = 𝔼ϕ is
`L_ϕ`-Lipschitz continuous" at `x^t − γ v_F(x^t)`): for `ℙ`-almost every `ξ`,
`‖ϕ(x, ξ) − ϕ(y, ξ)‖ ≤ L_ϕ ‖x − y‖` for all `x, y ∈ ℝ^d`. -/
def LipschitzGlobal (Lphi : ℝ) : Prop :=
  ∀ᵐ s ∂M.P, ∀ x y : Vec d, ‖M.phiVec x s - M.phiVec y s‖ ≤ Lphi * ‖x - y‖

/-- Assumption 2.3(a),(c) on all of `ℝ^d` (arXiv:2205.01774v3, p.10, and its use on p.40, "the
Lipschitz continuity of ∇g, i.e., g is smooth", at `x^t − γ v_F(x^t) ∉ 𝒳`): every `gᵢ` is
differentiable on `ℝ`, and the diagonal Jacobian is `S_g`-Lipschitz on `ℝ^d`. -/
def SmoothGlobal (Sg : ℝ) : Prop :=
  (∀ i y, DifferentiableAt ℝ (M.gc i) y) ∧
    ∀ x y : Vec d, ∀ i, |deriv (M.gc i) (x i) - deriv (M.gc i) (y i)| ≤ Sg * ‖x - y‖

/-- The *global model* used for the run-level displays of the proof of Theorem 3.2
(arXiv:2205.01774v3, Appendix C, pp.38–40): monotonicity of `ϕ` on `ℝ`, `L_ϕ`-Lipschitz continuity
of `ϕ` on `ℝ^d`, and an `S_g`-Lipschitz Jacobian of `g` on `ℝ^d`. -/
def GlobalModel (Lphi Sg : ℝ) : Prop :=
  M.MonotoneGlobal ∧ M.LipschitzGlobal Lphi ∧ M.SmoothGlobal Sg

end Model

end StochHiddenConvex


