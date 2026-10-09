-- Prove2me | Definitions.Def_YuanDGD_Sublinear_Setting
-- name    : YuanDGD_Sublinear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:19:41.038395+00:00
-- url     : https://prove2.me/theorems/99502ca8-162d-4586-a10d-5fa48637ebf6
-- title:
--   §2.1–§2.3, pp. 6–11 — the Lyapunov function ξ_α (8), the constant C of (17), the objective error r̄(k) and Theorem 2's threshold, on the shared DGD setting
-- statement:
--   The setting of decentralized gradient descent (DGD) of Yuan, Ling and Yin.
--
--   **Network and data.** There are $n \ge 2$ agents connected by an undirected graph $G$ on $\{1,\dots,n\}$. Agent $i$ privately holds a function $f_i : \mathbb R^p \to \mathbb R$, and together the agents solve the consensus problem
--   $$\min_{x \in \mathbb R^p} f(x) = \sum_{i=1}^n f_i(x). \qquad (2)$$
--   Its solution set is $\mathcal X^* = \{x : f(x) \le f(y)\ \forall y\}$.
--
--   **Mixing matrix.** $W = [w_{ij}] \in \mathbb R^{n\times n}$ is symmetric and doubly stochastic (nonnegative entries, every row and column sums to $1$). Its eigenvalues, counted with multiplicity and sorted, are $1 = \lambda_1(W) \ge \lambda_2(W) \ge \dots \ge \lambda_n(W) \ge -1$, and
--   $$\beta = \max\{|\lambda_2(W)|, |\lambda_n(W)|\}. \qquad (5)$$
--
--   **Assumption 1.** (a) Each $f_i$ is convex, differentiable, bounded below, and $\nabla f_i$ is Lipschitz with constant $L_{f_i} > 0$: $\|\nabla f_i(a) - \nabla f_i(b)\| \le L_{f_i}\|a-b\|$. (b) $G$ is connected, $w_{ij} \ne 0$ only if $i = j$ or $i, j$ are neighbours, $W$ is symmetric and doubly stochastic, and $\beta < 1$. We also require $n \ge 2$.
--
--   **Constants.** $L_h = \max_i L_{f_i}$, $L_{\bar f} = \frac1n\sum_i L_{f_i}$, $f_i^o = \inf_x f_i(x)$, and
--   $$D = \sqrt{2L_h\sum_{i=1}^n \big(f_i(0) - f_i^o\big)}. \qquad (10)$$
--
--   **The iteration.** Stacked vectors $[x_{(i)}] = [x_{(1)}; \dots; x_{(n)}] \in \mathbb R^{np}$ carry the Euclidean norm $\|[x_{(i)}]\| = (\sum_i \|x_{(i)}\|^2)^{1/2}$. DGD with stepsize $\alpha$ starts from $x_{(i)}(0) = 0$ and runs
--   $$x_{(i)}(k+1) = \sum_{j=1}^n w_{ij} x_{(j)}(k) - \alpha \nabla f_i(x_{(i)}(k)), \qquad i = 1,\dots,n. \qquad (4)$$
--   Derived quantities: $h(k) = [\nabla f_1(x_{(1)}(k)); \dots; \nabla f_n(x_{(n)}(k))]$, the mean $\bar x(k) = \frac1n\sum_i x_{(i)}(k)$, $g(k) = \frac1n\sum_i \nabla f_i(x_{(i)}(k))$, $\bar g(k) = \frac1n\sum_i \nabla f_i(\bar x(k))$, and $\bar f(y) = \frac1n\sum_i f_i(y)$ (16).
--
--   **Lyapunov function (8).**
--   $$\xi_\alpha([x_{(i)}]) = -\frac12\sum_{i,j=1}^n w_{ij}\, x_{(i)}^\top x_{(j)} + \sum_{i=1}^n\Big(\frac12\|x_{(i)}\|^2 + \alpha f_i(x_{(i)})\Big).$$
--
--   **Quantities of Theorem 2.** For a stack $[\tilde x_{(i)}]$ and a point $x^*$,
--   $$C = \frac{1}{\sqrt n}\Big(\|[x_{(i)}(0) - \tilde x_{(i)}]\| + \|[\tilde x_{(i)} - x^*]\|\Big) \qquad (17)$$
--   (with $x_{(i)}(0) = 0$), the objective error $\bar r(k) = \bar f(\bar x(k)) - \bar f(x^*)$, and the threshold $C\sqrt2\cdot \alpha L_h D/(1-\beta)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Everything above up to and including (16) — $\mathbb R^p$, stacks, the mixing step, $\lambda_n(W)$, $\beta$, Assumption 1, $L_h$, $L_{\bar f}$, $f_i^o$, $D$, the iteration, $h$, $\bar x$, $g$, $\bar g$, $\bar f$ and $\mathcal X^*$ — is the paper's shared setting module `YuanDGD.Linear.Setting` (namespace `YuanDGD.Linear`), which this module imports and opens; this module itself defines only $\xi_\alpha$, the constant stack $[x^*]$, $C$, $\bar r$ and the threshold. $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)` and stacks are `PiLp 2`, so stacked norms are Euclidean. Gradients are Mathlib's `gradient`. $\lambda_n(W)$ and $\beta$ are read from `Matrix.IsHermitian.eigenvalues₀` (sorted nonincreasingly, with multiplicity); they take the junk value $0$ when $W$ is not symmetric or $n < 2$, which never happens under Assumption 1. "Proper closed" in Assumption 1 (a) is automatic for a real-valued convex differentiable function and has no field; the "synchronized clock" is the iteration itself. $L_h$ is a supremum over the finite nonempty index set, i.e. the maximum. $f_i^o$ is the infimum of $f_i$ (the paper writes $f_i(x^o_{(i)})$ with $x^o_{(i)}$ a minimizer, which need not exist; the two agree whenever it does). The requirement $n \ge 2$ is added because $\lambda_2(W)$ needs two agents. $C$ is defined for a fixed $x^*$ (see Theorem 2).
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, pp. 1–11, (2), (4), (5), Assumption 1 (p. 4), stacked notation (p. 5), (8) (p. 6), (10) (p. 7), x̄ (p. 8), g, ḡ (p. 9), (16), r̄ (p. 10), (17) (p. 11), Theorem 2 (p. 10)

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

namespace YuanDGD.Sublinear

/-! The shared objects of the paper — `E`, `Stack`, `mix`, `lamN`, `beta`, `Assumption1`, `Lh`, `Lbar`,
`fo`, `D`, `dgd`, `xbar`, `hvec`, `gk`, `gbar`, `fbar`, `Xstar` — are those of
`Definitions.Def_YuanDGD_Linear_Setting` (namespace `YuanDGD.Linear`). This module adds the objects of
§2.1 and §2.3 used only by Theorem 2. -/

open YuanDGD.Linear

variable {n p : ℕ}

/-- The Lyapunov function (8):
`ξ_α([x₍ᵢ₎]) = −(1/2) Σᵢⱼ wᵢⱼ x₍ᵢ₎ᵀx₍ⱼ₎ + Σᵢ ((1/2)‖x₍ᵢ₎‖² + α fᵢ(x₍ᵢ₎))`. -/
noncomputable def xi (α : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (y : Stack n p) : ℝ :=
  -(1 / 2) * ∑ i, ∑ j, W i j * inner ℝ (y i) (y j) + ∑ i, ((1 / 2) * ‖y i‖ ^ 2 + α * f i (y i))

/-- The constant stack `[z; …; z] ∈ ℝⁿᵖ` (written `[x*]` in (17)). -/
noncomputable def constStack (z : E p) : Stack n p := WithLp.toLp 2 (fun _ => z)

/-- The constant `C` of (17) with `x₍ᵢ₎(0) = 0`, a fixed minimizer `[x̃₍ᵢ₎]` of `ξ_α` and a fixed `x*`:
`C = (1/√n)(‖[x₍ᵢ₎(0) − x̃₍ᵢ₎]‖ + ‖[x̃₍ᵢ₎ − x*]‖)`. -/
noncomputable def Cconst (xt : Stack n p) (xs : E p) : ℝ :=
  (1 / Real.sqrt n) * (‖(0 : Stack n p) - xt‖ + ‖xt - constStack xs‖)

/-- The objective error `r̄(k) = f̄(x̄(k)) − f̄*` with `f̄* = f̄(x*)` (p. 10). -/
noncomputable def rbar (f : Fin n → E p → ℝ) (x : ℕ → Stack n p) (xs : E p) (k : ℕ) : ℝ :=
  fbar f (xbar x k) - fbar f xs

/-- The threshold of Theorem 2 (p. 10): `C√2 · αL_hD/(1 − β)`. -/
noncomputable def threshold (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ) (Lf : Fin n → ℝ)
    (α C : ℝ) : ℝ :=
  C * Real.sqrt 2 * (α * Lh Lf * D f Lf / (1 - beta W))

end YuanDGD.Sublinear


