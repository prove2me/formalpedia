-- Prove2me | Definitions.Def_AdaptiveEM_Finite_Assumptions
-- name    : AdaptiveEM_Finite_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:55.687985+00:00
-- url     : https://prove2.me/theorems/6985a53e-a091-4659-b6be-1ba69182a503
-- title:
--   Assumptions 1–4, pp. 528–530 — local Lipschitz and linear growth, adaptive timestep condition (10), the family h^δ (11), one-sided and polynomial Lipschitz conditions
-- statement:
--   These are the four hypotheses on the coefficients and on the timestep function in §2.2 of Fang and Giles (2020). Throughout, $f:\mathbb R^m\to\mathbb R^m$ is the drift and $g:\mathbb R^m\to\mathbb R^{m\times d}$ the diffusion of the SDE $dX_t=f(X_t)\,dt+g(X_t)\,dW_t$; $\|x\|$ and $\langle x,y\rangle$ are the Euclidean norm and inner product on $\mathbb R^m$, and $\|A\|=(\sum_{i,j}A_{ij}^2)^{1/2}$ is the Frobenius norm of a matrix.
--
--   1. **Assumption 1** (local Lipschitz and linear growth), with constants $\alpha_1,\beta_1\ge 0$: for every $R>0$ there is $C_R$ such that $\|f(x)-f(y)\|+\|g(x)-g(y)\|\le C_R\|x-y\|$ whenever $\|x\|,\|y\|\le R$, and for all $x$
--   $$\langle x,f(x)\rangle\le\alpha_1\|x\|^2+\beta_1,\qquad \|g(x)\|^2\le\alpha_1\|x\|^2+\beta_1 .$$
--   2. **Assumption 2** (adaptive timestep), with constants $\alpha,\beta>0$: the timestep function $h:\mathbb R^m\to\mathbb R$ is continuous and strictly positive, and for all $x$
--   $$\langle x,f(x)\rangle+\tfrac12 h(x)\|f(x)\|^2\le\alpha\|x\|^2+\beta. \tag{10}$$
--   3. **Assumption 3**, for a horizon $T$ and a family $h^\delta$, $0<\delta\le 1$: for every such $\delta$ and every $x$
--   $$\delta\min(T,h(x))\le h^\delta(x)\le\min(\delta T,h(x)). \tag{11}$$
--   4. **Assumption 4** (Lipschitz properties): there is $\alpha>0$ such that for all $x,y$
--   $$\langle x-y,f(x)-f(y)\rangle\le\tfrac12\alpha\|x-y\|^2,\qquad \|g(x)-g(y)\|^2\le\tfrac12\alpha\|x-y\|^2,$$
--   and there are $\gamma,\mu,q>0$ with $\|f(x)-f(y)\|\le(\gamma(\|x\|^q+\|y\|^q)+\mu)\|x-y\|$.
--
--   Assumption 1 is the stability hypothesis on the SDE, Assumption 2 is the condition that makes an adaptive timestep stabilise the explicit Euler scheme for drifts of superlinear growth, Assumption 3 describes how the timesteps are refined as $\delta\to0$, and Assumption 4 is the hypothesis of the strong convergence rate.
--
--   **Formalization Note** Each assumption is a proposition with its constants as explicit arguments. The paper names the constants of both Assumption 1 and Assumption 2 $\alpha,\beta$; they are independent existentials, and here Assumption 1 takes $\alpha_1,\beta_1$ (nonnegative) and Assumption 2 takes $\alpha,\beta$ (positive). The positivity conditions on the constants are conjuncts of the propositions. $h$ is real-valued and its positivity is part of Assumption 2; $h^\delta$ is a function of $\delta\in\mathbb R$ and $x$, and (11) is required for $0<\delta\le1$ only. $\|x\|^q$ is a real power. Matrices are elements of the published Euclidean space indexed by $\mathrm{Fin}\,m\times\mathrm{Fin}\,d$, whose norm is the Frobenius norm.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), pp. 528–530, Assumptions 1–4, (7)–(14)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting

open scoped NNReal RealInnerProductSpace

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), Assumption 1, pp. 528–529 (local Lipschitz and linear growth), with its
own constants `α₁, β₁ ≥ 0`: (7) for every `R > 0` there is `C_R` with
`‖f x - f y‖ + ‖g x - g y‖ ≤ C_R ‖x - y‖` when `‖x‖, ‖y‖ ≤ R`;
(8) `⟪x, f x⟫ ≤ α₁ ‖x‖² + β₁`; (9) `‖g x‖² ≤ α₁ ‖x‖² + β₁` (Frobenius norm). -/
def Assumption1 {m d : ℕ} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (α₁ β₁ : ℝ) : Prop :=
  (∀ R : ℝ, 0 < R → ∃ C_R : ℝ, ∀ x y : SDEState m, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖f x - f y‖ + ‖g x - g y‖ ≤ C_R * ‖x - y‖) ∧
  0 ≤ α₁ ∧ 0 ≤ β₁ ∧
  (∀ x : SDEState m, ⟪x, f x⟫ ≤ α₁ * ‖x‖ ^ 2 + β₁) ∧
  (∀ x : SDEState m, ‖g x‖ ^ 2 ≤ α₁ * ‖x‖ ^ 2 + β₁)

/-- Fang–Giles (2020), Assumption 2, p. 529 (adaptive timestep), with its own constants
`α, β > 0`: `h` is continuous and strictly positive and (10)
`⟪x, f x⟫ + ½ h(x) ‖f x‖² ≤ α ‖x‖² + β` for all `x`. -/
def Assumption2 {m : ℕ} (f : SDEState m → SDEState m) (h : SDEState m → ℝ) (α β : ℝ) : Prop :=
  Continuous h ∧ (∀ x : SDEState m, 0 < h x) ∧ 0 < α ∧ 0 < β ∧
  ∀ x : SDEState m, ⟪x, f x⟫ + 1 / 2 * h x * ‖f x‖ ^ 2 ≤ α * ‖x‖ ^ 2 + β

/-- Fang–Giles (2020), Assumption 3, p. 530: the family `h^δ`, `0 < δ ≤ 1`, satisfies (11)
`δ min(T, h(x)) ≤ h^δ(x) ≤ min(δ T, h(x))` for all `x`. -/
def Assumption3 {m : ℕ} (T : ℝ) (h : SDEState m → ℝ) (hδ : ℝ → SDEState m → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ x : SDEState m,
    δ * min T (h x) ≤ hδ δ x ∧ hδ δ x ≤ min (δ * T) (h x)

/-- Fang–Giles (2020), Assumption 4, p. 530 (Lipschitz properties): `α > 0`,
(12) `⟪x - y, f x - f y⟫ ≤ ½ α ‖x - y‖²`, (13) `‖g x - g y‖² ≤ ½ α ‖x - y‖²`, and
(14) `‖f x - f y‖ ≤ (γ (‖x‖^q + ‖y‖^q) + μ) ‖x - y‖` with `γ, μ, q > 0` (real powers). -/
def Assumption4 {m d : ℕ} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (α γ μ q : ℝ) : Prop :=
  0 < α ∧
  (∀ x y : SDEState m, ⟪x - y, f x - f y⟫ ≤ 1 / 2 * α * ‖x - y‖ ^ 2) ∧
  (∀ x y : SDEState m, ‖g x - g y‖ ^ 2 ≤ 1 / 2 * α * ‖x - y‖ ^ 2) ∧
  0 < γ ∧ 0 < μ ∧ 0 < q ∧
  ∀ x y : SDEState m, ‖f x - f y‖ ≤ (γ * (‖x‖ ^ q + ‖y‖ ^ q) + μ) * ‖x - y‖

end AdaptiveEM.Finite


