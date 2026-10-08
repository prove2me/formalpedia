-- Prove2me | Definitions.Def_LeiBR_Sync_StochGame
-- name    : LeiBR_Sync_StochGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:22.386073+00:00
-- url     : https://prove2.me/theorems/3330cc13-c927-4097-8f63-3e3c8c731fe8
-- title:
--   Stochastic Nash game: expected payoffs, Assumption 1, the proximal BR map (2)/(7), the matrix $\Gamma$ (3)–(4) and Assumption 2
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $\xi:\Omega\to\mathbb R^d$ a random vector. Player $i$ has a sample cost $\psi_i(x;\xi)$ and the **expected payoff** $f_i(x)=\mathbb E[\psi_i(x;\xi)]$, and $\nabla_{x_i}\psi_i(x;s)$ denotes a sampled partial gradient. The partial gradient $\nabla_{x_i}f_i(x)$ is the gradient of $z\mapsto f_i(z,x_{-i})$ at $z=x_i$.
--
--   **Assumption 1** (with constants $M_i$):
--   1. every $X_i$ is closed, compact, convex and nonempty;
--   2. there are open convex sets $V_i\supseteq X_i$ such that $f_i$ is finite on $\prod_j V_j$, twice continuously differentiable on $\prod_j V_j$ as a function of the whole profile, and $z\mapsto f_i(z,y_{-i})$ is convex on $V_i$ for every $y\in X$;
--   3. for $x_{-i}\in X_{-i}$, $x_i\in V_i$ and every $\omega$, $\psi_i(\cdot,x_{-i};\xi(\omega))$ is differentiable at $x_i$ with gradient $\nabla_{x_i}\psi_i(x;\xi(\omega))$, this gradient is integrable, and $\nabla_{x_i}f_i(x)=\mathbb E[\nabla_{x_i}\psi_i(x;\xi)]$;
--   4. $M_i>0$ and $\mathbb E\|\nabla_{x_i}\psi_i(x;\xi)\|^2\le M_i^2$ for all $x\in X$.
--
--   For $\mu>0$, the **proximal best-response map** $\hat x$ is
--   $$\hat x_i(y)=\operatorname*{argmin}_{x_i\in X_i}\Big[f_i(x_i,y_{-i})+\frac\mu2\|x_i-y_i\|^2\Big],\qquad y\in X .$$
--   With
--   $$\zeta_{i,\min}=\inf_{x\in X}\lambda_{\min}\big(\nabla^2_{x_i}f_i(x)\big),\qquad \zeta_{ij,\max}=\sup_{x\in X}\big\|\nabla^2_{x_ix_j}f_i(x)\big\|\quad(j\ne i),$$
--   where $\lambda_{\min}(A)$ is the smallest eigenvalue of $(A+A^{T})/2$, the $N\times N$ matrix $\Gamma=[\gamma_{ij}]$ has
--   $$\gamma_{ii}=\frac{\mu}{\mu+\zeta_{i,\min}},\qquad \gamma_{ij}=\frac{\zeta_{ij,\max}}{\mu+\zeta_{i,\min}}\quad(j\neq i).$$
--   **Assumption 2** is $\|\Gamma\|<1$ for the spectral norm.
--
--   These are the standing hypotheses of every result in the paper: Assumption 1 makes each proximal BR problem a strongly convex stochastic program, and Assumption 2 makes the proximal BR map a contraction.
--
--   **Formalization Note** $\hat x$ is any function with $\hat x_i(y)\in X_i$ minimizing the proximal objective over $X_i$ for $y\in X$ (`IsProxBR`); under Assumption 1 the minimizer exists and is unique, so this pins $\hat x$ down on $X$. Assumption 1(b) is taken jointly in the profile ($C^2$ in $x$, not only in $x_i$), because $\zeta_{ij,\max}$ needs the mixed blocks $\nabla^2_{x_ix_j}f_i$. Convexity is taken on the open set $V_i$, which is the paper's "convex … over an open set containing $X_i$" and gives $\zeta_{i,\min}\ge0$. $\lambda_{\min}$ of the symmetric part is written as the infimum of the Rayleigh quotients $D^2f_i(x)(\iota_iv,\iota_iv)$ over unit $v$, and $\|\nabla^2_{x_ix_j}f_i(x)\|$ as the supremum of $|D^2f_i(x)(\iota_iu,\iota_jw)|$ over unit $u,w$; both sets are bounded because $X$ is compact and $D^2f_i$ is continuous. The spectral norm is the operator norm of `Matrix.toEuclideanCLM Γ`. Integrability hypotheses accompany every expectation, since Lean's integral of a non-integrable function is $0$.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, pp. 4–7, Notations, (SNash_i), Assumption 1, (2)–(4), (7), Assumption 2

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame

open MeasureTheory

namespace LeiBR.Sync

variable {N : ℕ} {n : Fin N → ℕ}

/-- The expected payoff `f_i(x) = E[ψ_i(x; ξ)] = ∫ ψ_i(x; ξ(ω)) dP(ω)` of (SNash_i). -/
noncomputable def payoff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ) (i : Fin N) (x : Profile n) : ℝ :=
  ∫ ω, ψ i x (ξ ω) ∂P

/-- The partial gradient `∇_{x_i} f_i(x)`: the gradient of `z ↦ f_i(z, x_{-i})` at `z = x_i`. -/
noncomputable def partialGrad (f : Fin N → Profile n → ℝ) (i : Fin N) (x : Profile n) :
    Strat n i :=
  gradient (fun z : Strat n i => f i (Function.update x i z)) (x i)

/-- Assumption 1 (p. 5), with the expected payoffs `f_i = payoff P ξ ψ i`, sampled partial
gradients `gψ i x s = ∇_{x_i} ψ_i(x; s)` and second-moment bounds `M i`.
(a) every `X i` is closed, compact, convex and nonempty;
(b) there are open convex sets `V i ⊇ X i` such that `f_i` is finite on `∏ V`, is twice
continuously differentiable (jointly in the whole profile) on `∏ V`, and `z ↦ f_i(z, y_{-i})`
is convex on `V i` for every `y ∈ X`;
(c) for `x_{-i} ∈ X_{-i}` and `x_i ∈ V i`, `ψ_i(·, x_{-i}; ξ(ω))` has gradient `gψ i x (ξ ω)`
at `x_i` for every `ω`, this gradient is integrable and `∇_{x_i} f_i(x) = E[∇_{x_i} ψ_i(x; ξ)]`;
(d) `M i > 0` and `E‖∇_{x_i} ψ_i(x; ξ)‖² ≤ M_i²` (with the integrand integrable) for `x ∈ X`. -/
def Assumption1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ}
    (ξ : Ω → EuclideanSpace ℝ (Fin d)) (X : ∀ i : Fin N, Set (Strat n i))
    (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ) :
    Prop :=
  (∀ i, IsClosed (X i) ∧ IsCompact (X i) ∧ Convex ℝ (X i) ∧ (X i).Nonempty) ∧
  ∃ V : ∀ i : Fin N, Set (Strat n i),
    (∀ i, IsOpen (V i) ∧ Convex ℝ (V i) ∧ X i ⊆ V i) ∧
    (∀ i, ∀ x ∈ Set.univ.pi V, Integrable (fun ω => ψ i x (ξ ω)) P) ∧
    (∀ i, ContDiffOn ℝ 2 (payoff P ξ ψ i) (Set.univ.pi V)) ∧
    (∀ i, ∀ y ∈ stratSet X,
      ConvexOn ℝ (V i) (fun z : Strat n i => payoff P ξ ψ i (Function.update y i z))) ∧
    (∀ i (x : Profile n), (∀ j, j ≠ i → x j ∈ X j) → x i ∈ V i →
      (∀ ω, HasGradientAt (fun z : Strat n i => ψ i (Function.update x i z) (ξ ω))
          (gψ i x (ξ ω)) (x i)) ∧
      Integrable (fun ω => gψ i x (ξ ω)) P ∧
      partialGrad (payoff P ξ ψ) i x = ∫ ω, gψ i x (ξ ω) ∂P) ∧
    (∀ i, 0 < M i ∧ ∀ x ∈ stratSet X,
      Integrable (fun ω => ‖gψ i x (ξ ω)‖ ^ 2) P ∧ ∫ ω, ‖gψ i x (ξ ω)‖ ^ 2 ∂P ≤ M i ^ 2)

/-- The proximal best-response map (2)/(7): for every `y ∈ X` and every player `i`,
`xhat y i ∈ X i` minimizes `z ↦ f_i(z, y_{-i}) + (μ/2)‖z - y_i‖²` over `X i`. -/
def IsProxBR (X : ∀ i : Fin N, Set (Strat n i)) (f : Fin N → Profile n → ℝ) (μ : ℝ)
    (xhat : Profile n → Profile n) : Prop :=
  ∀ y ∈ stratSet X, ∀ i : Fin N, xhat y i ∈ X i ∧
    IsMinOn (fun z : Strat n i => f i (Function.update y i z) + μ / 2 * ‖z - y i‖ ^ 2) (X i)
      (xhat y i)

/-- The second derivative `D²g(x)` as a bilinear map on profiles. -/
noncomputable def hess (g : Profile n → ℝ) (x : Profile n) :
    Profile n →L[ℝ] Profile n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ g) x

/-- `ζ_{i,min} = inf_{x ∈ X} λ_min(∇²_{x_i} f_i(x))` of (4), written as the infimum of the
Rayleigh quotients `vᵀ ∇²_{x_i} f_i(x) v = D²f_i(x)(ι_i v, ι_i v)` over unit vectors `v ∈ ℝ^{n_i}`
(`ι_i v = Pi.single i v`); this is the smallest eigenvalue of the symmetric part. -/
noncomputable def zetaMin (X : ∀ i : Fin N, Set (Strat n i)) (f : Fin N → Profile n → ℝ)
    (i : Fin N) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ stratSet X, ∃ v : Strat n i, ‖v‖ = 1 ∧
    r = hess (f i) x (Pi.single i v) (Pi.single i v)}

/-- `ζ_{ij,max} = sup_{x ∈ X} ‖∇²_{x_i x_j} f_i(x)‖` of (4), the spectral norm of the
`(i, j)` Hessian block written as `sup |uᵀ ∇²_{x_i x_j} f_i(x) w|` over unit `u ∈ ℝ^{n_i}`,
`w ∈ ℝ^{n_j}`. -/
noncomputable def zetaMax (X : ∀ i : Fin N, Set (Strat n i)) (f : Fin N → Profile n → ℝ)
    (i j : Fin N) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ stratSet X, ∃ u : Strat n i, ∃ w : Strat n j, ‖u‖ = 1 ∧ ‖w‖ = 1 ∧
    r = |hess (f i) x (Pi.single i u) (Pi.single j w)|}

/-- The matrix `Γ` of (3): `γ_ii = μ/(μ + ζ_{i,min})`, `γ_ij = ζ_{ij,max}/(μ + ζ_{i,min})`. -/
noncomputable def Gamma (X : ∀ i : Fin N, Set (Strat n i)) (f : Fin N → Profile n → ℝ)
    (μ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i = j then μ / (μ + zetaMin X f i) else zetaMax X f i j / (μ + zetaMin X f i)

/-- The spectral norm `‖A‖` (operator norm on `ℝ^N` with the Euclidean norm). -/
noncomputable def specNorm (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖

/-- Assumption 2 (p. 7): `‖Γ‖ < 1` (spectral norm). -/
def Assumption2 (X : ∀ i : Fin N, Set (Strat n i)) (f : Fin N → Profile n → ℝ) (μ : ℝ) :
    Prop :=
  specNorm (Gamma X f μ) < 1

end LeiBR.Sync


