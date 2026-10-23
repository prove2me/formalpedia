-- Prove2me | Definitions.Def_AggDiscountStopping_OneBarrier_Setting
-- name    : AggDiscountStopping_OneBarrier_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:27.205686+00:00
-- url     : https://prove2.me/theorems/a543ac5d-d367-4e89-b574-1cf3a223ee0d
-- title:
--   §2–§4, pp. 4–17 — aggregated-discount stopping model, diffusion encoding, J, Θ, equilibria, V, C-(i)–C-(iii), Laplace representation
-- statement:
--   This module sets up the time-inconsistent stopping problem of Deng, Yu and Zhang under aggregation of diverse discount rates.
--
--   1. **Model** (§2, §4). A drift $\mu$ and a volatility $\sigma$ on $\mathbb R$, a strike $K$, the law $F_\rho$ of the random discount rate $\rho$, and an **attitude function** $\phi$. The payoff is the Put payoff $g(x)=(K-x)^+$. The standing assumptions are: $K>0$; $F_\rho$ is a probability law concentrated on $[0,\infty)$; $\mu$ and $\sigma$ are Lipschitz; $\sigma^2(x)>0$ for $x>0$.
--   2. **Conditions of §4.** For a fixed $\epsilon>0$ the speed density and scale function are
--   $$m(y)=\frac{1}{\sigma^2(y)}\exp\Big(\int_\epsilon^y\frac{2\mu(z)}{\sigma^2(z)}dz\Big),\qquad u(x)=\int_\epsilon^x\exp\Big(-\int_\epsilon^y\frac{2\mu(z)}{\sigma^2(z)}dz\Big)dy,$$
--   and $\phi_1(x)=\big(\mu(x)+\sqrt{\mu^2(x)+2r\sigma^2(x)}\big)/\sigma^2(x)$ (which depends on $r$).
--      - **C-(i)**: $\mu(x)\ge0$ for $x\ge0$.
--      - **C-(ii)-1**: $\phi_1'(x)<0$ for $x>0$ (for every $r\ge0$), and $\limsup_{x\to\infty}(\mu(x)+1)/\sigma^2(x)<\infty$.
--      - **C-(ii)-2**: $I_1=\int_\epsilon^\infty u'(x)\big(\int_\epsilon^x m(y)dy\big)dx=+\infty$ and $I_2=\int_\epsilon^\infty u(x)m(x)dx=+\infty$.
--      - **C-(iii)**: $\phi$ is continuous on $[0,\infty)$, $C^1$ on $(0,\infty)$, strictly increasing, and $x\mapsto\phi'(x)x$ is increasing.
--   3. **The process.** A family of paths $X^x_t(\omega)$, $t\ge0$, on a probability space, started at $X^x_0=x$, continuous, and non-negative when $x\ge0$. The **entry time** of a set $R$ is $\tau(x,R)=\inf\{t>0: X^x_t\in R\}$ (strictly positive times), and $\tau^x_a=\tau(x,\{a\})$. We write $H(r,a,x)=\ln\mathbb E[e^{-r\tau^x_a}]$.
--   4. **Aggregated payoff and equilibria** (pp. 6–7). For a Borel set $R$,
--   $$J(x,R)=\int_0^\infty\phi\Big(\mathbb E\big[e^{-r\tau(x,R)}g(X^x_{\tau(x,R)})\big]\Big)dF_\rho(r),$$
--   where the discounted payoff is $0$ on paths that never enter $R$. The stopping and indifference regions are $S_R=\{x\ge0:\phi(g(x))>J(x,R)\}$ and $I_R=\{x\ge0:\phi(g(x))=J(x,R)\}$, the policy improvement operator is $\Theta(R)=S_R\cup(I_R\cap R)$, and $R$ is an **equilibrium** (Definition 3.1) if it is Borel and $\Theta(R)=R$. The value is $V(x,R)=\phi(g(x))\vee J(x,R)$ (p. 16). A barrier $a$ is **optimal among one-barrier equilibria** if $[0,a]$ is an equilibrium and $V(x,[0,a])\ge V(x,[0,b])$ for every $x\ge0$ and every equilibrium $[0,b]$ with $b>0$ (Definition 4.1 restricted to regions $[0,b]$).
--   5. **Laplace representation** (Remark 4.3). A family $(\varphi_r)_{r\ge0}$ of positive, decreasing, $C^2$ solutions on $(0,\infty)$ of
--   $$\tfrac12\sigma^2(x)u''(x)+\mu(x)u'(x)=ru(x)\qquad(4.1)$$
--   such that $\mathbb E[e^{-r\tau^x_a}]=\varphi_r(x)/\varphi_r(a)$ for all $0<a\le x$ and $r\ge0$. With it, $\tilde m_r=-\varphi_r'/\varphi_r$ and $G(a)=\int_0^\infty\varphi_r'(a)/\varphi_r(a)\,dF_\rho(r)$ ((4.8)).
--
--   These objects are shared by every statement of the mission: the threshold characterization of one-barrier equilibria (Theorem 4.8) and the analytic lemmas on $\varphi_r$ that lead to it.
--
--   **Formalization Note** Mathlib has no stochastic differential equations, so $X$ is not asserted to solve $dX_t=\mu(X_t)dt+\sigma(X_t)dW_t$. The process enters only through path regularity (`Diffusion.Valid`) and through the hitting-time Laplace representation of Remark 4.3 (`IsLaplaceRep`), which the paper imports from Borodin–Salminen and which is a hypothesis of every statement that needs the process; the strong Markov property and time-homogeneity are not used and not encoded. Time is $\mathbb R_{\ge0}$. The entry time is an infimum over $t>0$; a path that never enters $R$ contributes $0$, the paper's $\mathbf 1\{\tau<\infty\}$ convention. $S_R$ and $I_R$ are taken on the state space $x\ge0$. "Increasing" means non-decreasing (p. 9). C-(ii)-1 is read on $x>0$ for every $r\ge0$ (printed "$x\ge0$"; $\phi_1$ is undefined at $0$ in the paper's examples), and its limsup as an eventual upper bound. $I_1,I_2$ are lower Lebesgue integrals of their nonnegative integrands. C-(iii)'s "$C^1$" is read as continuity on $[0,\infty)$ plus $C^1$ on $(0,\infty)$, which admits $x^p/p$, $0<p\le1$; $\ln x$ is excluded because $\phi(g(x))$ must be real for $x\ge K$. The attitude $\phi$ is `att` and the ODE solution $\varphi_r$ is `φ r`.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, §2 (pp. 4–7: Definition 2.1, J(x, R), Θ, S_R, I_R p. 6), Definition 3.1 (p. 7), §4 (p. 9: Put payoff, SDE, scale and speed, C-(i), C-(ii); p. 10: C-(ii)-1, C-(ii)-2, C-(iii); p. 11: Remark 4.3, (4.1), m̃_r; p. 16: V, Definition 4.1; p. 17: (4.8))

import Mathlib

namespace AggDiscountStopping.OneBarrier

open MeasureTheory Set Filter Topology
open scoped NNReal

/-- The model of §2 and §4: drift `μ`, volatility `σ`, strike `K` of the Put payoff,
the law `F` of the discount rate `ρ` (the paper's `F_ρ`), and the attitude function `att`
(the paper's `ϕ`). -/
structure Model where
  μ : ℝ → ℝ
  σ : ℝ → ℝ
  K : ℝ
  F : Measure ℝ
  att : ℝ → ℝ

namespace Model

/-- The Put payoff `g(x) = (K − x)⁺`, p. 9. -/
noncomputable def g (M : Model) (x : ℝ) : ℝ := max (M.K - x) 0

/-- Standing assumptions of §2 (the discount rate `ρ` has a law `F_ρ` on `[0, ∞)`) and of
§4, p. 9 (`K > 0`; `μ`, `σ` Lipschitz; `σ²(x) > 0` for `x > 0`). -/
structure Valid (M : Model) : Prop where
  K_pos : 0 < M.K
  F_prob : IsProbabilityMeasure M.F
  F_nonneg : M.F (Iio 0) = 0
  μ_lip : ∃ L, LipschitzWith L M.μ
  σ_lip : ∃ L, LipschitzWith L M.σ
  σ_sq_pos : ∀ x, 0 < x → 0 < M.σ x ^ 2

/-- Condition C-(i), p. 9: `μ(x) ≥ 0` for all `x ≥ 0`. -/
def CondI (M : Model) : Prop := ∀ x, 0 ≤ x → 0 ≤ M.μ x

/-- `ϕ₁(x) = (μ(x) + √(μ²(x) + 2rσ²(x)))/σ²(x)`, C-(ii), p. 9, as a function of `(r, x)`. -/
noncomputable def phi1 (M : Model) (r x : ℝ) : ℝ :=
  (M.μ x + Real.sqrt (M.μ x ^ 2 + 2 * r * M.σ x ^ 2)) / M.σ x ^ 2

/-- Condition C-(ii)-1, p. 10: `ϕ₁′(x) < 0` (read on `x > 0`, for every `r ≥ 0`) and
`limsup_{x→∞} (μ(x) + 1)/σ²(x) < ∞` (an eventual upper bound). -/
def CondII1 (M : Model) : Prop :=
  (∀ r, 0 ≤ r → ∀ x, 0 < x → deriv (M.phi1 r) x < 0) ∧
    ∃ C x₀ : ℝ, ∀ x, x₀ ≤ x → (M.μ x + 1) / M.σ x ^ 2 ≤ C

/-- The scale density `u′(x) = exp(−∫_ε^x 2μ(z)/σ²(z) dz)`, p. 9. -/
noncomputable def scaleDensity (M : Model) (ε x : ℝ) : ℝ :=
  Real.exp (-∫ z in ε..x, 2 * M.μ z / M.σ z ^ 2)

/-- The speed density `m(y) = exp(∫_ε^y 2μ(z)/σ²(z) dz)/σ²(y)`, p. 9. -/
noncomputable def speedDensity (M : Model) (ε y : ℝ) : ℝ :=
  Real.exp (∫ z in ε..y, 2 * M.μ z / M.σ z ^ 2) / M.σ y ^ 2

/-- The scale function `u(x) = ∫_ε^x u′(y) dy`, p. 9. -/
noncomputable def scale (M : Model) (ε x : ℝ) : ℝ := ∫ y in ε..x, M.scaleDensity ε y

/-- Condition C-(ii)-2, p. 10: `I₁ = I₂ = +∞`, where
`I₁ = ∫_ε^∞ u′(x) (∫_ε^x m(y) dy) dx` and `I₂ = ∫_ε^∞ u(x) m(x) dx`, as lower Lebesgue
integrals of the (nonnegative) integrands. -/
def CondII2 (M : Model) (ε : ℝ) : Prop :=
  (∫⁻ x in Ioi ε, ENNReal.ofReal (M.scaleDensity ε x * ∫ y in ε..x, M.speedDensity ε y)) = ⊤ ∧
    (∫⁻ x in Ioi ε, ENNReal.ofReal (M.scale ε x * M.speedDensity ε x)) = ⊤

/-- Condition C-(iii), p. 10: the attitude function `ϕ` is continuous on `[0, ∞)` and `C¹` on
`(0, ∞)`, strictly increasing on `[0, ∞)`, and `x ↦ ϕ′(x) x` is increasing on `(0, ∞)`. -/
def CondIII (M : Model) : Prop :=
  ContinuousOn M.att (Ici 0) ∧ ContDiffOn ℝ 1 M.att (Ioi 0) ∧
    StrictMonoOn M.att (Ici 0) ∧ MonotoneOn (fun x => deriv M.att x * x) (Ioi 0)

end Model

/-- The diffusion, encoded by its paths on a measurable space `Ω` with measure `P`:
`X x t ω` is the state at time `t ≥ 0` of the path started at `x`. -/
structure Diffusion (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  X : ℝ → ℝ≥0 → Ω → ℝ

namespace Diffusion

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Path regularity: `P` is a probability measure, every path starts at its initial state,
paths are continuous (§2), and paths started in `[0, ∞)` stay in `[0, ∞)` (§4, p. 9). -/
structure Valid (D : Diffusion Ω) : Prop where
  prob : IsProbabilityMeasure D.P
  start : ∀ x ω, D.X x 0 ω = x
  cont : ∀ x ω, Continuous fun t => D.X x t ω
  nonneg : ∀ x, 0 ≤ x → ∀ t ω, 0 ≤ D.X x t ω

/-- The path started at `x` enters `R` at some time `t > 0`. -/
def enters (D : Diffusion Ω) (x : ℝ) (R : Set ℝ) (ω : Ω) : Prop :=
  ∃ t : ℝ≥0, 0 < t ∧ D.X x t ω ∈ R

/-- The entry time `τ(x, R) = inf{t > 0 : X^x_t ∈ R}`, p. 6 (used only under `enters`). -/
noncomputable def entryTime (D : Diffusion Ω) (x : ℝ) (R : Set ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t : ℝ≥0 | 0 < t ∧ D.X x t ω ∈ R}

open Classical in
/-- `e^{−rτ^x_a} 1{τ^x_a < ∞}` with `τ^x_a = inf{t > 0 : X^x_t = a}` (Proposition 4.2). -/
noncomputable def hitDisc (D : Diffusion Ω) (r a x : ℝ) (ω : Ω) : ℝ :=
  if D.enters x {a} ω then Real.exp (-r * (D.entryTime x {a} ω : ℝ)) else 0

/-- `E[e^{−rτ^x_a}]`, Proposition 4.2. -/
noncomputable def hitLaplace (D : Diffusion Ω) (r a x : ℝ) : ℝ := ∫ ω, D.hitDisc r a x ω ∂D.P

/-- `H(r, a, x) = ln E[e^{−rτ^x_a}]`, Proposition 4.2. -/
noncomputable def H (D : Diffusion Ω) (r a x : ℝ) : ℝ := Real.log (D.hitLaplace r a x)

end Diffusion

variable {Ω : Type*} [MeasurableSpace Ω]

open Classical in
/-- `e^{−rτ(x,R)} g(X^x_{τ(x,R)})`, and `0` when the path never enters `R`
(the paper's `1{τ < ∞}` convention). -/
noncomputable def discPayoff (M : Model) (D : Diffusion Ω) (r x : ℝ) (R : Set ℝ) (ω : Ω) : ℝ :=
  if D.enters x R ω then
    Real.exp (-r * (D.entryTime x R ω : ℝ)) * M.g (D.X x (D.entryTime x R ω) ω)
  else 0

/-- `J(x, R) = ∫_0^∞ ϕ(E[e^{−rτ(x,R)} g(X^x_{τ(x,R)})]) dF_ρ(r)`, p. 6. -/
noncomputable def J (M : Model) (D : Diffusion Ω) (x : ℝ) (R : Set ℝ) : ℝ :=
  ∫ r, M.att (∫ ω, discPayoff M D r x R ω ∂D.P) ∂M.F

/-- The stopping region `S_R = {x ≥ 0 : ϕ(g(x)) > J(x, R)}`, p. 6. -/
def stopRegion (M : Model) (D : Diffusion Ω) (R : Set ℝ) : Set ℝ :=
  {x | 0 ≤ x ∧ J M D x R < M.att (M.g x)}

/-- The indifference region `I_R = {x ≥ 0 : ϕ(g(x)) = J(x, R)}`, p. 6. -/
def indiffRegion (M : Model) (D : Diffusion Ω) (R : Set ℝ) : Set ℝ :=
  {x | 0 ≤ x ∧ M.att (M.g x) = J M D x R}

/-- The policy improvement operator `Θ(R) = S_R ∪ (I_R ∩ R)`, p. 6. -/
def Theta (M : Model) (D : Diffusion Ω) (R : Set ℝ) : Set ℝ :=
  stopRegion M D R ∪ (indiffRegion M D R ∩ R)

/-- Definition 3.1, p. 7: an equilibrium is a Borel set `R` with `Θ(R) = R`. -/
def IsEquilibrium (M : Model) (D : Diffusion Ω) (R : Set ℝ) : Prop :=
  MeasurableSet R ∧ Theta M D R = R

/-- `V(x, R) = ϕ(g(x)) ∨ J(x, R)`, p. 16. -/
noncomputable def Vval (M : Model) (D : Diffusion Ω) (x : ℝ) (R : Set ℝ) : ℝ :=
  max (M.att (M.g x)) (J M D x R)

/-- Definition 4.1, p. 16, restricted to one-barrier regions: `[0, a]` is an equilibrium and
`V(x, [0, a]) ≥ V(x, [0, b])` for every `x ≥ 0` and every equilibrium `[0, b]`, `b > 0`. -/
def IsOptimalOneBarrier (M : Model) (D : Diffusion Ω) (a : ℝ) : Prop :=
  IsEquilibrium M D (Icc 0 a) ∧ ∀ b, 0 < b → IsEquilibrium M D (Icc 0 b) →
    ∀ x, 0 ≤ x → Vval M D x (Icc 0 b) ≤ Vval M D x (Icc 0 a)

/-- Remark 4.3: `ψ` is a positive, decreasing, `C²` solution on `(0, ∞)` of the ODE (4.1)
`½σ²(x)u″(x) + μ(x)u′(x) = r u(x)`. -/
structure IsDecreasingSolution (M : Model) (r : ℝ) (ψ : ℝ → ℝ) : Prop where
  pos : ∀ x, 0 < x → 0 < ψ x
  smooth : ContDiffOn ℝ 2 ψ (Ioi 0)
  ode : ∀ x, 0 < x → 1 / 2 * M.σ x ^ 2 * deriv (deriv ψ) x + M.μ x * deriv ψ x = r * ψ x
  anti : AntitoneOn ψ (Ioi 0)

/-- Remark 4.3 (Borodin–Salminen), taken as a hypothesis: for every `r ≥ 0`, `φ r` is a
positive decreasing `C²` solution of (4.1), and `E[e^{−rτ^x_a}] = φ_r(x)/φ_r(a)` for
`0 < a ≤ x`. -/
structure IsLaplaceRep (M : Model) (D : Diffusion Ω) (φ : ℝ → ℝ → ℝ) : Prop where
  sol : ∀ r, 0 ≤ r → IsDecreasingSolution M r (φ r)
  laplace : ∀ r, 0 ≤ r → ∀ a x, 0 < a → a ≤ x → D.hitLaplace r a x = φ r x / φ r a

/-- `m̃(x) = −ψ′(x)/ψ(x)`, proof of Proposition 4.4, p. 11 (`m̃_r = −m_r`, `m_r = φ′_r/φ_r`). -/
noncomputable def mtilde (ψ : ℝ → ℝ) (x : ℝ) : ℝ := -deriv ψ x / ψ x

/-- `G(a) = ∫_0^∞ φ′_r(a)/φ_r(a) dF_ρ(r)`, (4.8) via Remark 4.3, p. 17. -/
noncomputable def G (M : Model) (φ : ℝ → ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ r, deriv (φ r) a / φ r a ∂M.F

end AggDiscountStopping.OneBarrier


