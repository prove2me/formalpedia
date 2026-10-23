-- Prove2me | Definitions.Def_ErgSingMFG_Abelian_Analytic
-- name    : ErgSingMFG_Abelian_Analytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:30.381821+00:00
-- url     : https://prove2.me/theorems/4b78d6ec-83b1-4577-8ae6-6a43ac4beb62
-- title:
--   §2–§4, pp. 4–9 — model data, S′, m′, Ŝ′, m̂′, generators (2.7)–(2.8), fundamental solutions of (2.9)–(2.10), natural boundaries, Assumptions 2.1, 2.2, 3.3, 4.1, 4.3
-- statement:
--   The analytic layer of the stationary singular-control mean field games of Cao, Dianetti and Ferrari. Throughout, $\mathbb R_+=(0,\infty)$.
--
--   A **model** consists of a drift $b$ and a volatility $\sigma$ (used on $\mathbb R_+$), a running profit $\pi(x,\theta)$ (used on $\mathbb R_+^2$), weight functions $F,f$ (used on $[0,\infty)$), and the constant $c$ of Assumption 4.3. Write $\pi_x$ and $\pi_{x\theta}$ for the partial derivatives of $\pi$. The **scale and speed densities** of the uncontrolled diffusion $X$ and of the auxiliary diffusion $\widehat X$ with drift $b+\sigma\sigma'$ are
--   $$S'(x)=\exp\Big(-\int_1^x\frac{2b(z)}{\sigma^2(z)}dz\Big),\quad m'(x)=\frac{2}{\sigma^2(x)S'(x)},\quad \widehat S'(x)=\exp\Big(-\int_1^x\frac{2b(z)+2\sigma(z)\sigma'(z)}{\sigma^2(z)}dz\Big),\quad \widehat m'(x)=\frac{2}{\sigma^2(x)\widehat S'(x)}.$$
--   The **generators** are $\mathcal L_Xu=\tfrac12\sigma^2u''+bu'$ (2.7) and $\mathcal L_{\widehat X}u=\tfrac12\sigma^2u''+(b+\sigma\sigma')u'$ (2.8). A **decreasing (increasing) fundamental solution** of $\mathcal L_Xu=ru$ (2.9) is a positive $C^2$ solution on $\mathbb R_+$ tending to $0$ at $+\infty$ (at $0$); a decreasing fundamental solution $\widehat\varphi_r$ of $\mathcal L_{\widehat X}u=(r-b')u$ (2.10) is a positive $C^2$ solution tending to $0$ at $+\infty$.
--
--   The boundaries $0$ and $+\infty$ of a diffusion with scale density $s$ and speed density $\mu$ are **natural** when the four Feller integrals $\int_1^\infty\mu(y)\int_1^ys\,dy$, $\int_1^\infty s(y)\int_1^y\mu\,dy$, $\int_0^1\mu(y)\int_y^1s\,dy$, $\int_0^1s(y)\int_y^1\mu\,dy$ are all infinite.
--
--   The **assumptions** are:
--   1. Assumption 2.1: $b,\sigma$ are $C^1$ on $\mathbb R_+$, $\sigma>0$, $b$ and $\sigma$ are globally Lipschitz on $\mathbb R_+$, and $\sigma\sigma'$ is locally Lipschitz;
--   2. Assumption 2.2: $\int_a^\infty m'(y)dy<\infty$ for every $a>0$;
--   3. the requirements of §2.1 (`FundReq`): $0$ and $\infty$ are natural for $X$ and for $\widehat X$, and for every $r>0$, $\varphi_r'(x)\to-\infty$ as $x\downarrow0$ and $\psi_r'(x)\to+\infty$ as $x\uparrow\infty$;
--   4. Assumption 3.3: $\pi\ge0$ is $C^2$ on $\mathbb R_+^2$; $\pi(\cdot,\theta)$ is concave and nondecreasing; $\pi_{x\theta}<0$; $\pi_x(x,\theta)\to+\infty$ as $\theta\downarrow0$ and $\to0$ as $\theta\uparrow\infty$; for $0<a<b$ there is a positive $h^{a,b}$, integrable on every $(\kappa,\infty)$, with $|\pi_{x\theta}(x,\theta)|\widehat m'(x)\le h^{a,b}(x)$ for $\theta\in(a,b)$; $F,f\ge0$ are continuous on $[0,\infty)$ and $C^1$ on $\mathbb R_+$ with $F',f'>0$, satisfy for some $\beta\in(0,1)$, $C>0$ the growth bounds $f(x)\le C(1+|x|^\beta)$, $F(x)\le C(1+|x|^{1/\beta})$, $|F(y)-F(x)|\le C(1+|x|+|y|)^{1/\beta-1}|y-x|$, and tend to $+\infty$;
--   5. Assumption 4.1 at rate $r$: $r-b'\ge2c>0$ for some $c$, and for every $\theta>0$ there is $\widehat x_r(\theta)>0$ such that $\pi_x(x,\theta)-r+b'(x)$ is positive below, zero at, and negative above $\widehat x_r(\theta)$;
--   6. Assumption 4.3: $b'<-2c<0$, and the same single crossing for $\pi_x+b'$ at a point $\widehat x_0(\theta)$.
--
--   **Formalization Note.** Derivatives of functions of the state are taken within $(0,\infty)$; $\pi_x,\pi_{x\theta},b',\sigma'$ are `deriv`, used only at points of the open set where the functions are $C^1$/$C^2$. The base point of $S'$ and $\widehat S'$ is $x_o=1$ (the paper leaves it arbitrary; every statement is invariant). Assumption 3.3(i) is read with $F,f$ continuous on $[0,\infty)$ and $C^1$ with positive derivative on $(0,\infty)$, so that the paper's benchmark $f(x)=x^\beta$, $F(y)=y^{1/\beta}$ is an instance. Natural boundaries are Feller's integral tests (lower Lebesgue integrals in $[0,\infty]$); the limits (2.11)–(2.14) of the paper are their consequences.
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, pp. 4–9, (2.1), (2.7)–(2.10), Assumptions 2.1, 2.2, 3.3, 4.1, 4.3, §2.1 boundary requirements (p. 6)

import Mathlib

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace ErgSingMFG.Abelian

/-- The model data of Cao–Dianetti–Ferrari (§2–§4), without hypotheses:
* `b` the drift and `σ` the volatility of the state equation (2.1), used on `ℝ₊ = (0, ∞)`;
* `π` the running profit `π(x, θ)` of (3.1)–(3.2), used on `ℝ₊ × ℝ₊`;
* `F` and `f` the weight functions of the mean `θ(μ) = F(∫ f dμ)` (3.4), used on `[0, ∞)`;
* `c` the constant of Assumption 4.3 (it fixes the parameter domain `(−c, 1)` of §5). -/
structure Model where
  /-- the drift `b` -/
  b : ℝ → ℝ
  /-- the volatility `σ` -/
  σ : ℝ → ℝ
  /-- the running profit `π(x, θ)` -/
  π : ℝ → ℝ → ℝ
  /-- the outer weight `F` of (3.4) -/
  F : ℝ → ℝ
  /-- the inner weight `f` of (3.4) -/
  f : ℝ → ℝ
  /-- the constant `c` of Assumption 4.3 -/
  c : ℝ

/-- The partial derivative `π_x(x, θ)`. -/
noncomputable def πx (m : Model) (x θ : ℝ) : ℝ := deriv (fun y => m.π y θ) x

/-- The mixed partial derivative `π_{xθ}(x, θ) = ∂_θ π_x(x, θ)`. -/
noncomputable def πxθ (m : Model) (x θ : ℝ) : ℝ := deriv (fun t => πx m x t) θ

/-- The scale density of `X` (p. 5), with base point `x_o = 1`:
`S′(x) = exp(−∫₁ˣ 2b(z)/σ²(z) dz)`. -/
noncomputable def Sp (m : Model) (x : ℝ) : ℝ :=
  Real.exp (-∫ z in (1 : ℝ)..x, 2 * m.b z / m.σ z ^ 2)

/-- The speed density of `X` (p. 6): `m′(x) = 2/(σ²(x) S′(x))`. -/
noncomputable def mp (m : Model) (x : ℝ) : ℝ := 2 / (m.σ x ^ 2 * Sp m x)

/-- The scale density of `X̂` (p. 6), with base point `x_o = 1`:
`Ŝ′(x) = exp(−∫₁ˣ (2b(z) + 2σ(z)σ′(z))/σ²(z) dz)`. -/
noncomputable def SHat (m : Model) (x : ℝ) : ℝ :=
  Real.exp (-∫ z in (1 : ℝ)..x, (2 * m.b z + 2 * m.σ z * deriv m.σ z) / m.σ z ^ 2)

/-- The speed density of `X̂` (p. 6): `m̂′(x) = 2/(σ²(x) Ŝ′(x))`. -/
noncomputable def mHat (m : Model) (x : ℝ) : ℝ := 2 / (m.σ x ^ 2 * SHat m x)

/-- The generator (2.7) of `X`: `(𝓛_X u)(x) = ½σ²(x)u″(x) + b(x)u′(x)`, derivatives taken within
`(0, ∞)`. -/
noncomputable def genX (m : Model) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  m.σ x ^ 2 / 2 * iteratedDerivWithin 2 u (Ioi 0) x + m.b x * derivWithin u (Ioi 0) x

/-- The generator (2.8) of `X̂`: `(𝓛_X̂ u)(x) = ½σ²(x)u″(x) + (b(x) + σ(x)σ′(x))u′(x)`, derivatives
taken within `(0, ∞)`. -/
noncomputable def genXHat (m : Model) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  m.σ x ^ 2 / 2 * iteratedDerivWithin 2 u (Ioi 0) x
    + (m.b x + m.σ x * deriv m.σ x) * derivWithin u (Ioi 0) x

/-- `φ` is a decreasing fundamental solution `φ_r` of (2.9) `𝓛_X u − r u = 0` on `(0, ∞)`:
`φ` is `C²` and positive on `(0, ∞)`, solves the ODE there, and tends to `0` at `+∞`. -/
def IsDecrFund (m : Model) (r : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Ioi 0) ∧ (∀ x > 0, 0 < φ x) ∧ (∀ x > 0, genX m φ x = r * φ x) ∧
    Tendsto φ atTop (𝓝 0)

/-- `ψ` is an increasing fundamental solution `ψ_r` of (2.9) `𝓛_X u − r u = 0` on `(0, ∞)`:
`ψ` is `C²` and positive on `(0, ∞)`, solves the ODE there, and tends to `0` as `x ↓ 0`. -/
def IsIncrFund (m : Model) (r : ℝ) (ψ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 ψ (Ioi 0) ∧ (∀ x > 0, 0 < ψ x) ∧ (∀ x > 0, genX m ψ x = r * ψ x) ∧
    Tendsto ψ (𝓝[>] 0) (𝓝 0)

/-- `φ` is a decreasing fundamental solution `φ̂_r` of (2.10) `𝓛_X̂ u − (r − b′)u = 0` on `(0, ∞)`:
`φ` is `C²` and positive on `(0, ∞)`, solves the ODE there, and tends to `0` at `+∞`. -/
def IsDecrFundHat (m : Model) (r : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Ioi 0) ∧ (∀ x > 0, 0 < φ x) ∧
    (∀ x > 0, genXHat m φ x = (r - deriv m.b x) * φ x) ∧ Tendsto φ atTop (𝓝 0)

/-- Feller's test: both boundaries `0` and `+∞` of a regular diffusion on `(0, ∞)` with scale density
`s` and speed density `μ` are **natural**. With `S[u, v] = ∫ᵤᵛ s` and `M[u, v] = ∫ᵤᵛ μ`, the four
Feller integrals are infinite:
`∫₁^∞ μ(y) S[1, y] dy = ∫₁^∞ s(y) M[1, y] dy = ∞` (boundary `∞`) and
`∫₀¹ μ(y) S[y, 1] dy = ∫₀¹ s(y) M[y, 1] dy = ∞` (boundary `0`). -/
def NaturalBdry (s μ : ℝ → ℝ) : Prop :=
  (∫⁻ y in Ioi (1 : ℝ), ENNReal.ofReal (μ y * ∫ z in (1 : ℝ)..y, s z)) = ⊤ ∧
  (∫⁻ y in Ioi (1 : ℝ), ENNReal.ofReal (s y * ∫ z in (1 : ℝ)..y, μ z)) = ⊤ ∧
  (∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (μ y * ∫ z in y..(1 : ℝ), s z)) = ⊤ ∧
  (∫⁻ y in Ioo (0 : ℝ) 1, ENNReal.ofReal (s y * ∫ z in y..(1 : ℝ), μ z)) = ⊤

/-- Assumption 2.1 (p. 5): `b : ℝ₊ → ℝ` and `σ : ℝ₊ → ℝ₊` are continuously differentiable (so
`σ > 0`), `b` and `σ` are globally Lipschitz on `ℝ₊`, and `σσ′` is locally Lipschitz on `ℝ₊`. -/
def Asm21 (m : Model) : Prop :=
  ContDiffOn ℝ 1 m.b (Ioi 0) ∧ ContDiffOn ℝ 1 m.σ (Ioi 0) ∧ (∀ x > 0, 0 < m.σ x) ∧
  (∃ L : ℝ≥0, LipschitzOnWith L m.b (Ioi 0) ∧ LipschitzOnWith L m.σ (Ioi 0)) ∧
  LocallyLipschitzOn (Ioi 0) (fun x => m.σ x * deriv m.σ x)

/-- Assumption 2.2 (p. 6): `∫ₐ^∞ m′(y) dy < ∞` for every `a > 0`. -/
def Asm22 (m : Model) : Prop := ∀ a > 0, IntegrableOn (mp m) (Ioi a)

/-- The requirements of §2.1 (p. 6): `0` and `+∞` are natural boundaries for `X` and for `X̂`, and,
for every `r > 0`, `lim_{x↓0} φ′_r(x) = −∞` and `lim_{x↑∞} ψ′_r(x) = +∞` (for every choice of the
fundamental solutions). -/
def FundReq (m : Model) : Prop :=
  NaturalBdry (Sp m) (mp m) ∧ NaturalBdry (SHat m) (mHat m) ∧
  (∀ r > 0, ∀ φ, IsDecrFund m r φ → Tendsto (deriv φ) (𝓝[>] 0) atBot) ∧
  (∀ r > 0, ∀ ψ, IsIncrFund m r ψ → Tendsto (deriv ψ) atTop atTop)

/-- Assumption 3.3 (pp. 7–8), with (i) read as: `F, f : [0, ∞) → [0, ∞)` continuous, `C¹` on
`(0, ∞)` with `F′, f′ > 0` there.
1. `π ≥ 0` on `ℝ₊²` and `π ∈ C²(ℝ₊²)`;
2. (π-i) `π(·, θ)` is concave and nondecreasing on `ℝ₊` for each `θ > 0`;
3. (π-ii) `π_{xθ} < 0` on `ℝ₊²`;
4. (π-iii) for each `x > 0`, `π_x(x, θ) → +∞` as `θ ↓ 0` and `π_x(x, θ) → 0` as `θ ↑ ∞`;
5. (π-iv) for `0 < a < b < ∞` there is `h^{a,b} : ℝ₊ → ℝ₊` with `|π_{xθ}(x, θ)| m̂′(x) ≤ h^{a,b}(x)`
   for `x > 0`, `θ ∈ (a, b)`, and `h^{a,b} ∈ L¹(κ, ∞)` for every `κ > 0`;
6. (i) the regularity of `F, f` above, and for some `β ∈ (0, 1)` and `C > 0`, for all `x, y > 0`:
   `f(x) ≤ C(1 + |x|^β)`, `F(x) ≤ C(1 + |x|^{1/β})`,
   `|F(y) − F(x)| ≤ C(1 + |x| + |y|)^{1/β − 1}|y − x|`;
7. (ii) `F(y) → ∞` and `f(y) → ∞` as `y ↑ ∞`. -/
def Asm33 (m : Model) : Prop :=
  (∀ x > 0, ∀ θ > 0, 0 ≤ m.π x θ) ∧
  ContDiffOn ℝ 2 (fun p : ℝ × ℝ => m.π p.1 p.2) (Ioi 0 ×ˢ Ioi 0) ∧
  (∀ θ > 0, ConcaveOn ℝ (Ioi 0) (fun x => m.π x θ) ∧ MonotoneOn (fun x => m.π x θ) (Ioi 0)) ∧
  (∀ x > 0, ∀ θ > 0, πxθ m x θ < 0) ∧
  (∀ x > 0, Tendsto (fun θ => πx m x θ) (𝓝[>] 0) atTop ∧
    Tendsto (fun θ => πx m x θ) atTop (𝓝 0)) ∧
  (∀ a b : ℝ, 0 < a → a < b → ∃ h : ℝ → ℝ, (∀ x > 0, 0 < h x) ∧
    (∀ x > 0, ∀ θ ∈ Ioo a b, |πxθ m x θ| * mHat m x ≤ h x) ∧
    ∀ κ > 0, IntegrableOn h (Ioi κ)) ∧
  ContinuousOn m.F (Ici 0) ∧ ContinuousOn m.f (Ici 0) ∧
  (∀ x ≥ 0, 0 ≤ m.F x ∧ 0 ≤ m.f x) ∧
  ContDiffOn ℝ 1 m.F (Ioi 0) ∧ ContDiffOn ℝ 1 m.f (Ioi 0) ∧
  (∀ x > 0, 0 < deriv m.F x ∧ 0 < deriv m.f x) ∧
  (∃ β ∈ Ioo (0 : ℝ) 1, ∃ C > (0 : ℝ), ∀ x > 0, ∀ y > 0,
    m.f x ≤ C * (1 + |x| ^ β) ∧ m.F x ≤ C * (1 + |x| ^ (1 / β)) ∧
    |m.F y - m.F x| ≤ C * (1 + |x| + |y|) ^ (1 / β - 1) * |y - x|) ∧
  Tendsto m.F atTop atTop ∧ Tendsto m.f atTop atTop

/-- The single-crossing pattern of Assumption 4.1(ii) at rate `r` (and of Assumption 4.3(ii) at
`r = 0`): `x̂ > 0` and `π_x(x, θ) − r + b′(x)` is `> 0` for `0 < x < x̂`, `= 0` at `x̂`, `< 0` for
`x > x̂`. -/
def xHatProp (m : Model) (r θ xh : ℝ) : Prop :=
  0 < xh ∧ (∀ x > 0, x < xh → 0 < πx m x θ - r + deriv m.b x) ∧
    πx m xh θ - r + deriv m.b xh = 0 ∧ (∀ x > xh, πx m x θ - r + deriv m.b x < 0)

/-- Assumption 4.1 (p. 8) at the rate `r`: (i) `r − b′(x) ≥ 2c > 0` on `ℝ₊` for a constant `c > 0`;
(ii) for every `θ > 0` there is `x̂_r(θ)` with the single-crossing pattern `xHatProp`. -/
def Asm41 (m : Model) (r : ℝ) : Prop :=
  (∃ c > (0 : ℝ), ∀ x > 0, 2 * c ≤ r - deriv m.b x) ∧ ∀ θ > 0, ∃ xh, xHatProp m r θ xh

/-- Assumption 4.3 (p. 9), with the model's constant `c`: (i) `c > 0` and `b′(x) < −2c` on `ℝ₊`;
(ii) for every `θ > 0` there is `x̂₀(θ)` with the single-crossing pattern of `π_x + b′`. -/
def Asm43 (m : Model) : Prop :=
  0 < m.c ∧ (∀ x > 0, deriv m.b x < -2 * m.c) ∧ ∀ θ > 0, ∃ xh, xHatProp m 0 θ xh

end ErgSingMFG.Abelian


