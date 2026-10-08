-- Prove2me | Definitions.Def_CondatPD_PPA_Setting
-- name    : CondatPD_PPA_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:15:18.74192+00:00
-- url     : https://prove2.me/theorems/c8c50be5-dee7-4893-a248-78bb082f8c9d
-- title:
--   §2–§4, pp. 2–13 — smooth term (2), solutions of (6), Algorithms 3.1–3.2, the forms of P and P′, the operator A
-- statement:
--   Throughout, $\mathcal X$ and $\mathcal Y$ are real Hilbert spaces, $L:\mathcal X\to\mathcal Y$ is a bounded linear operator with adjoint $L^*$ and operator norm $\|L\|$, and $\Gamma_0(\mathcal H)$ is the set of proper, lower semicontinuous, convex functions $\mathcal H\to\mathbb R\cup\{+\infty\}$. This module fixes the objects of Condat's primal–dual splitting method.
--
--   1. **Fenchel–Rockafellar conjugate.** For $J:\mathcal H\to[-\infty,+\infty]$,
--   $$J^*(s)=\sup_{s'\in\mathcal H}\big[\langle s,s'\rangle-J(s')\big],$$
--   a supremum of extended reals, so $J^*(s)=+\infty$ is allowed.
--   2. **Smooth term (2).** $F:\mathcal X\to\mathbb R$ satisfies the standing assumption with constant $\beta\in[0,+\infty[$ if $F$ is convex, differentiable on $\mathcal X$, and $\|\nabla F(x)-\nabla F(x')\|\le\beta\|x-x'\|$ for all $x,x'$.
--   3. **Solutions of (6).** A pair $(\hat x,\hat y)\in\mathcal X\times\mathcal Y$ solves
--   $$0\in\partial G(\hat x)+L^*\hat y+\nabla F(\hat x),\qquad 0\in-L\hat x+\partial H^*(\hat y),$$
--   that is, $-L^*\hat y-\nabla F(\hat x)\in\partial G(\hat x)$ and $L\hat x\in\partial H^*(\hat y)$, where $\partial J(u)=\{v:\ J(u)+\langle v,u'-u\rangle\le J(u')\ \forall u'\}$.
--   4. **Algorithm 3.1 (9).** Given $\tau,\sigma$, relaxation parameters $(\rho_n)$, error terms $e_{F,n},e_{G,n}\in\mathcal X$, $e_{H,n}\in\mathcal Y$, and maps $P_G=\mathrm{prox}_{\tau G}$, $P_H=\mathrm{prox}_{\sigma H^*}$, a run is any pair of sequences $(x_n),(y_n)$ with arbitrary $(x_0,y_0)$ such that for every $n$
--   $$\tilde x_{n+1}=P_G\big(x_n-\tau(\nabla F(x_n)+e_{F,n})-\tau L^*y_n\big)+e_{G,n},\qquad \tilde y_{n+1}=P_H\big(y_n+\sigma L(2\tilde x_{n+1}-x_n)\big)+e_{H,n},$$
--   $$(x_{n+1},y_{n+1})=\rho_n(\tilde x_{n+1},\tilde y_{n+1})+(1-\rho_n)(x_n,y_n).$$
--   5. **Algorithm 3.2 (10).** The same with the roles swapped: $\tilde y_{n+1}=P_H(y_n+\sigma Lx_n)+e_{H,n}$, then $\tilde x_{n+1}=P_G\big(x_n-\tau(\nabla F(x_n)+e_{F,n})-\tau L^*(2\tilde y_{n+1}-y_n)\big)+e_{G,n}$, and the same relaxation step.
--   6. **The quadratic forms of $P$ (20) and $P'$ (44).** On $\mathcal Z=\mathcal X\times\mathcal Y$ with $\langle z,z'\rangle_I=\langle x,x'\rangle+\langle y,y'\rangle$ (19),
--   $$\langle z,Pz\rangle_I=\big\langle x,\tfrac1\tau x-L^*y\big\rangle+\big\langle y,-Lx+\tfrac1\sigma y\big\rangle,\qquad \langle z,P'z\rangle_I=\big\langle x,\tfrac1\tau x+L^*y\big\rangle+\big\langle y,Lx+\tfrac1\sigma y\big\rangle .$$
--   7. **The operator $A$ of (22)** on the Hilbert space $\mathcal Z_I$:
--   $$A(x,y)=\big(\partial G(x)+L^*y\big)\times\big(-Lx+\partial H^*(y)\big).$$
--
--   These objects are shared by every statement of the mission: Theorem 3.2, Remark 3.2 and the milestones of its proof.
--
--   **Formalization Note** Functions with values in $\mathbb R\cup\{+\infty\}$ are `EReal`-valued. The conjugate is not redefined here: it is the published `MoreauProx.Characterization.conj`, $J^*(s)=\sup_{x}[\langle x,s\rangle-J(x)]$ computed in `EReal`. $\Gamma_0$ is the published `IsProperClosedConvex`, and the subdifferential is the published `InertialFB.IFB.IsSubgradient`, which also requires $J(u)<+\infty$ (automatic for a proper $J$ with nonempty $\partial J(u)$). Proximity operators are not defined here: the theorems take maps $P_G,P_H$ with the published `IsProx` property. A run fixes no initial point. The operator $P$ itself is not built; it enters only through its quadratic form. $\mathcal Z_I$ is `WithLp 2 (X × Y)`, whose inner product is exactly (19). Algorithm runs are stated with a `let` for $\tilde x_{n+1},\tilde y_{n+1}$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), pp. 2–5, (1), (2), (6), Algorithms 3.1–3.2 (9)–(10); p. 10, (19), (20), (22); p. 13, (44)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_MoreauProx_Characterization_GammaZero

open InnerProductSpace

namespace CondatPD.PPA

/-! The Fenchel–Rockafellar conjugate `J*(s) = sup_{s'} [⟨s, s'⟩ − J(s')]` (Condat 2013, §2, p. 2) is the
published `MoreauProx.Characterization.conj`, an `EReal` supremum. -/

/-- The standing assumption on the smooth term `F` of problem (1) (p. 3, (2)): `F : 𝒳 → ℝ` is convex,
differentiable on `𝒳`, and `∇F` is `β`-Lipschitz for some `β ∈ [0, +∞[`. -/
def IsSmoothTerm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (β : ℝ) (F : X → ℝ) : Prop :=
  ConvexOn ℝ Set.univ F ∧ Differentiable ℝ F ∧ 0 ≤ β ∧
    ∀ x x' : X, ‖gradient F x - gradient F x'‖ ≤ β * ‖x - x'‖

section TwoSpaces

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- `(x̂, ŷ)` solves the monotone inclusion (6) (p. 3):
`0 ∈ ∂G(x̂) + L*ŷ + ∇F(x̂)` and `0 ∈ −Lx̂ + ∂H*(ŷ)`, written as
`−L*ŷ − ∇F(x̂) ∈ ∂G(x̂)` and `Lx̂ ∈ ∂H*(ŷ)`. -/
def IsPDSolution (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (xh : X) (yh : Y) : Prop :=
  InertialFB.IFB.IsSubgradient G xh (-(ContinuousLinearMap.adjoint L yh) - gradient F xh) ∧
    InertialFB.IFB.IsSubgradient (MoreauProx.Characterization.conj H) yh (L xh)

/-- A run `(xₙ, yₙ)` of Algorithm 3.1 (p. 4, (9)) with proximal parameters `τ, σ`, relaxation
parameters `ρ`, error terms `eF, eG, eH`, and maps `PG = prox_{τG}`, `PH = prox_{σH*}`:
for every `n`,
1. `x̃ₙ₊₁ = PG(xₙ − τ(∇F(xₙ) + e_{F,n}) − τL*yₙ) + e_{G,n}`,
2. `ỹₙ₊₁ = PH(yₙ + σL(2x̃ₙ₊₁ − xₙ)) + e_{H,n}`,
3. `(xₙ₊₁, yₙ₊₁) = ρₙ(x̃ₙ₊₁, ỹₙ₊₁) + (1 − ρₙ)(xₙ, yₙ)`.
The initial point `(x 0, y 0)` is arbitrary. -/
def IsAlg31Run (F : X → ℝ) (L : X →L[ℝ] Y) (τ σ : ℝ) (PG : X → X) (PH : Y → Y)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y) (x : ℕ → X) (y : ℕ → Y) : Prop :=
  ∀ n : ℕ,
    let xt := PG (x n - τ • (gradient F (x n) + eF n) - τ • ContinuousLinearMap.adjoint L (y n)) + eG n
    let yt := PH (y n + σ • L ((2 : ℝ) • xt - x n)) + eH n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧ y (n + 1) = ρ n • yt + (1 - ρ n) • y n

/-- A run `(xₙ, yₙ)` of Algorithm 3.2 (p. 5, (10)): for every `n`,
1. `ỹₙ₊₁ = PH(yₙ + σLxₙ) + e_{H,n}`,
2. `x̃ₙ₊₁ = PG(xₙ − τ(∇F(xₙ) + e_{F,n}) − τL*(2ỹₙ₊₁ − yₙ)) + e_{G,n}`,
3. `(xₙ₊₁, yₙ₊₁) = ρₙ(x̃ₙ₊₁, ỹₙ₊₁) + (1 − ρₙ)(xₙ, yₙ)`. -/
def IsAlg32Run (F : X → ℝ) (L : X →L[ℝ] Y) (τ σ : ℝ) (PG : X → X) (PH : Y → Y)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y) (x : ℕ → X) (y : ℕ → Y) : Prop :=
  ∀ n : ℕ,
    let yt := PH (y n + σ • L (x n)) + eH n
    let xt := PG (x n - τ • (gradient F (x n) + eF n)
      - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - y n)) + eG n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧ y (n + 1) = ρ n • yt + (1 - ρ n) • y n

/-- The quadratic form `⟨z, Pz⟩_I` of the operator `P` of (20) (p. 10) at `z = (x, y)`:
`P(x, y) = ((1/τ)x − L*y, −Lx + (1/σ)y)` and `⟨z, z'⟩_I = ⟨x, x'⟩ + ⟨y, y'⟩` (19). -/
noncomputable def qP (τ σ : ℝ) (L : X →L[ℝ] Y) (x : X) (y : Y) : ℝ :=
  ⟪x, τ⁻¹ • x - ContinuousLinearMap.adjoint L y⟫_ℝ + ⟪y, -(L x) + σ⁻¹ • y⟫_ℝ

/-- The quadratic form `⟨z, P′z⟩_I` of the operator `P′` of (44) (p. 13) at `z = (x, y)`:
`P′(x, y) = ((1/τ)x + L*y, Lx + (1/σ)y)`. -/
noncomputable def qP' (τ σ : ℝ) (L : X →L[ℝ] Y) (x : X) (y : Y) : ℝ :=
  ⟪x, τ⁻¹ • x + ContinuousLinearMap.adjoint L y⟫_ℝ + ⟪y, L x + σ⁻¹ • y⟫_ℝ

/-- The operator `A` of (22) (p. 10) on `𝒵_I = 𝒳 × 𝒴` with the inner product (19), encoded as
`WithLp 2 (X × Y)`: `A(x, y) = (∂G(x) + L*y) × (−Lx + ∂H*(y))`. -/
def opA (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y) :
    WithLp 2 (X × Y) → Set (WithLp 2 (X × Y)) :=
  fun z => {w | ∃ (u : X) (v : Y), InertialFB.IFB.IsSubgradient G z.fst u ∧
    InertialFB.IFB.IsSubgradient (MoreauProx.Characterization.conj H) z.snd v ∧
    w = WithLp.toLp 2 (u + ContinuousLinearMap.adjoint L z.snd, v - L z.fst)}

end TwoSpaces

end CondatPD.PPA


