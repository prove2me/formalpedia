-- Prove2me | Definitions.Def_PINNNeuralTangent_Basic
-- name    : PINNNeuralTangent_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T10:10:45.159892+00:00
-- url     : https://prove2.me/theorems/80082e1e-1b53-4a6c-a5ce-34b16282c071
-- title:
--   PINN loss, gradient flow, neural tangent kernel and the one-hidden-layer model problem
-- statement:
--   Objects of Sections 2-4 and Appendices C-D of Wang, Yu and Perdikaris (2020).
--
--   1. **Parameters and partial derivatives.** The parameters of a network form a finite family $\theta=(\theta_p)_{p\in P}$. For a function $F$ of the parameters, $\partial F/\partial\theta_p$ is the derivative of $s\mapsto F(\theta \text{ with } \theta_p \text{ replaced by } s)$ at $s=\theta_p$. $\|v\|_2=(\sum_i v_i^2)^{1/2}$, and $\|A\|_2=\sup_{\|v\|_2\le1}\|Av\|_2$ is the spectral norm.
--   2. **PINN loss and gradient flow (eqs. 3.3-3.7).** For a network $u(x,\theta)$ on $\mathbb R^d$, a differential operator $\mathcal L$, boundary points $x_b^1,\dots,x_b^{N_b}$ and collocation points $x_r^1,\dots,x_r^{N_r}$,
--   $$\mathcal L(\theta)=\tfrac12\sum_{i=1}^{N_b}|u(x_b^i,\theta)-g(x_b^i)|^2+\tfrac12\sum_{j=1}^{N_r}|\mathcal Lu(x_r^j,\theta)-f(x_r^j)|^2 .$$
--   A curve $\theta(t)$, $t\in[0,T]$, is a gradient flow if $\theta'(t)=-\nabla\mathcal L(\theta(t))$, with one-sided derivatives at the endpoints.
--   3. **NTK of a PINN (eq. 3.9).** $(K_{uu})_{ij}=\langle\partial_\theta u(x_b^i,\theta),\partial_\theta u(x_b^j,\theta)\rangle$, $(K_{ur})_{ij}=\langle\partial_\theta u(x_b^i,\theta),\partial_\theta\mathcal Lu(x_r^j,\theta)\rangle$, $(K_{ru})_{ij}=\langle\partial_\theta \mathcal Lu(x_r^i,\theta),\partial_\theta u(x_b^j,\theta)\rangle$, $(K_{rr})_{ij}=\langle\partial_\theta\mathcal Lu(x_r^i,\theta),\partial_\theta\mathcal Lu(x_r^j,\theta)\rangle$, where $\langle\cdot,\cdot\rangle$ sums over all parameters. $K=\begin{bmatrix}K_{uu}&K_{ur}\\K_{ru}&K_{rr}\end{bmatrix}$.
--   4. **One-hidden-layer network (eqs. 4.2-4.3).** For width $N$ the parameters are $W^{(0)},W^{(1)},b^{(0)}\in\mathbb R^N$ and $b^{(1)}\in\mathbb R$, and
--   $$u(x,\theta)=\frac1{\sqrt N}\sum_{k=1}^NW^{(1)}_k\sigma(W^{(0)}_kx+b^{(0)}_k)+b^{(1)},\qquad u_{xx}(x,\theta)=\partial_x^2u(x,\theta).$$
--   At initialization all $3N+1$ parameters are independent $\mathcal N(0,1)$.
--   5. **Model problem (eq. 4.1).** $u_{xx}=f$ on $\Omega=(a,b)$, $u=g$ on $\partial\Omega=\{a,b\}$, with $a<b$, $x_b^i\in\{a,b\}$, $x_r^j\in(a,b)$. Its loss and NTK are those of items 2-3 with $\mathcal Lu=u_{xx}$.
--   6. **Gaussian-process kernels (eqs. 2.4, 2.5, 4.6).** With $w,b$ independent standard Gaussians, $\Sigma^{(1)}(x,x')=E[\sigma(wx+b)\sigma(wx'+b)]+1$, $\dot\Sigma^{(1)}(x,x')=E[\dot\sigma(wx+b)\dot\sigma(wx'+b)]$, $\Sigma^{(1)}_{xx}(x,x')=E[w^4\ddot\sigma(wx+b)\ddot\sigma(wx'+b)]$. A probability measure $\gamma$ on $\mathbb R^n$ is $\mathcal N(0,C)$ if $\int e^{i\langle t,y\rangle}d\gamma(y)=e^{-t^\top Ct/2}$ for all $t$.
--   7. **Limiting NTK (Appendix C).** Writing $\sigma^{(k)}$ for $\sigma^{(k)}(wx+b)$ and $\sigma'^{(k)}$ for $\sigma^{(k)}(wx'+b)$:
--   $$\Theta_{uu}(x,x')=\dot\Sigma^{(1)}(x,x')\,xx'+E[\sigma\sigma']+\dot\Sigma^{(1)}(x,x')+1,$$
--   $$\Theta_{ur}(x,x')=E[w^2\sigma^{(1)}\sigma'^{(3)}]xx'+2E[w\sigma^{(1)}\sigma'^{(2)}]x+E[w^2\sigma\,\sigma'^{(2)}]+E[w^2\sigma^{(1)}\sigma'^{(3)}],$$
--   $$\Theta_{rr}(x,x')=E[w^4\sigma^{(3)}\sigma'^{(3)}]xx'+2E[w^3\sigma^{(3)}\sigma'^{(2)}]x+2E[w^3\sigma'^{(3)}\sigma^{(2)}]x'+4E[w^2\sigma^{(2)}\sigma'^{(2)}]+E[w^4\sigma^{(2)}\sigma'^{(2)}]+E[w^4\sigma^{(3)}\sigma'^{(3)}],$$
--   and $K^*=\begin{bmatrix}\Theta_{uu}(x_b^i,x_b^j)&\Theta_{ur}(x_b^i,x_r^j)\\\Theta_{ur}(x_b^j,x_r^i)&\Theta_{rr}(x_r^i,x_r^j)\end{bmatrix}$.
--   8. **Hypotheses of Theorem 4.4.** A family of trajectories $\theta_N(t)$, one for each width $N$, satisfies (i) if $|\theta_N(t)_p|\le C$ for all $N$, $t\in[0,T]$ and parameters $p$. It satisfies (ii) as printed if $\int_0^T|\sum_i(u(x_b^i,\theta_N(\tau))-g(x_b^i))|\,d\tau\le C$ and $\int_0^T|\sum_j(u_{xx}(x_r^j,\theta_N(\tau))-f(x_r^j))|\,d\tau\le C$ for all $N$. It satisfies (ii) in the form the proof uses if the same bounds hold with the absolute value inside the sums. The activation satisfies (iii) if $\sigma$ is smooth and $|\sigma^{(k)}|\le C$ for $k=0,\dots,4$. In each case $C$ does not depend on $N$.
--
--   **Formalization Note** $\Sigma^{(1)}$ and $\dot\Sigma^{(1)}$ are written as expectations over $(wx+b,wx'+b)$, which has the covariance $\Lambda^{(1)}$ of eq. (2.4). The limits $\Theta$ are the expectations that the law-of-large-numbers steps of Appendix C produce. Several of the closed forms printed there are wrong, and these definitions replace them; see the notes on Theorem 4.3. Condition (ii) is recorded in both forms: the printed form is used only in Lemma D.1, which does not depend on it.
-- source:
--   Wang, Yu and Perdikaris, When and why PINNs fail to train: A neural tangent kernel perspective, arXiv:2007.14527v1 (2020), Sections 2-4 (eqs. (2.4), (2.5), (3.3)-(3.9), (4.1)-(4.3), (4.6)), Theorem 4.4 hypotheses (i)-(iii) p. 6, Appendix C pp. 20-23

import Mathlib

/-!
Wang, Yu and Perdikaris, *When and why PINNs fail to train: A neural tangent kernel perspective*,
arXiv:2007.14527v1 (2020): the PINN loss, gradient flow and neural tangent kernel of Section 3
(eqs. (3.3)-(3.9)), the one-hidden-layer network of the model problem of Section 4
(eqs. (4.1)-(4.3)), the Gaussian-process and limiting kernels of Sections 2 and 4 and Appendix C,
and the hypotheses (i)-(iii) of Theorem 4.4.
-/

open MeasureTheory ProbabilityTheory
open scoped ContDiff

noncomputable section

namespace PINNNeuralTangent

section General

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Remark 3.2: the partial derivative `∂F/∂θ_p` of a function of the network parameters
`θ = (θ_p)_{p ∈ P}` with respect to the single parameter `θ_p`. -/
def pd (F : (P → ℝ) → ℝ) (θ : P → ℝ) (p : P) : ℝ :=
  deriv (fun s : ℝ => F (Function.update θ p s)) (θ p)

/-- Euclidean norm `‖v‖₂ = (∑ᵢ vᵢ²)^{1/2}` of a finite vector. -/
def l2norm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- Spectral norm `‖A‖₂ = sup_{‖v‖₂ ≤ 1} ‖Av‖₂` of a real square matrix (Theorem 4.4). -/
def specNorm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  sSup ((fun v : ι → ℝ => l2norm (A.mulVec v)) '' {v | l2norm v ≤ 1})

/-- Eq. (3.9) and Remark 3.2: a block of the NTK of a PINN,
`(K_{FG})_{ij}(θ) = ⟨∂F_i/∂θ, ∂G_j/∂θ⟩ = ∑_p ∂F_i/∂θ_p · ∂G_j/∂θ_p`, for two families of network
outputs `F_i, G_j` viewed as functions of the parameters. -/
def ntkBlock {I J : Type*} (F : I → (P → ℝ) → ℝ) (G : J → (P → ℝ) → ℝ) (θ : P → ℝ) :
    Matrix I J ℝ :=
  fun i j => ∑ p, pd (F i) θ p * pd (G j) θ p

/-- Lemma 3.1 and Remark 3.3: the NTK of a PINN, `K = [[K_uu, K_ur], [K_ru, K_rr]]`, built from the
boundary outputs `U_i(θ) = u(x_b^i, θ)` and the operator outputs `R_j(θ) = 𝓛u(x_r^j, θ)`. -/
def pinnNTK {Nb Nr : ℕ} (U : Fin Nb → (P → ℝ) → ℝ) (R : Fin Nr → (P → ℝ) → ℝ) (θ : P → ℝ) :
    Matrix (Fin Nb ⊕ Fin Nr) (Fin Nb ⊕ Fin Nr) ℝ :=
  Matrix.fromBlocks (ntkBlock U U θ) (ntkBlock U R θ) (ntkBlock R U θ) (ntkBlock R R θ)

/-- Eqs. (3.4)-(3.6): the PINN loss `L(θ) = ½ ∑ᵢ |U_i(θ) - g_i|² + ½ ∑ⱼ |R_j(θ) - f_j|²`, where
`U_i(θ) = u(x_b^i, θ)`, `R_j(θ) = 𝓛u(x_r^j, θ)`, `g_i = g(x_b^i)` and `f_j = f(x_r^j)`. -/
def pinnLoss {Nb Nr : ℕ} (U : Fin Nb → (P → ℝ) → ℝ) (R : Fin Nr → (P → ℝ) → ℝ)
    (gb : Fin Nb → ℝ) (fr : Fin Nr → ℝ) (θ : P → ℝ) : ℝ :=
  (1 / 2) * ∑ i, (U i θ - gb i) ^ 2 + (1 / 2) * ∑ j, (R j θ - fr j) ^ 2

/-- Eq. (3.7): `θ(t)` solves the gradient flow `dθ/dt = -∇L(θ)` on the time interval `[0, T]`. -/
def IsGradFlow (L : (P → ℝ) → ℝ) (θ : ℝ → P → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt θ (fun p => -pd L (θ t) p) (Set.Icc 0 T) t

/-- Section 3: the network output on the boundary points, `θ ↦ u(x_b^i, θ)`, for a network
`u(x, θ)` on `ℝ^d`. -/
def bdryOutputs {d Nb : ℕ} (u : (Fin d → ℝ) → (P → ℝ) → ℝ) (xb : Fin Nb → Fin d → ℝ) :
    Fin Nb → (P → ℝ) → ℝ :=
  fun i θ => u (xb i) θ

/-- Eq. (3.3): `𝓛u(x, θ)`, the differential operator `𝓛` applied to the network `x ↦ u(x, θ)`
and evaluated at `x`. -/
def opOutput {d : ℕ} (Lop : ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ)
    (u : (Fin d → ℝ) → (P → ℝ) → ℝ) (x : Fin d → ℝ) (θ : P → ℝ) : ℝ :=
  Lop (fun y => u y θ) x

/-- Section 3: the operator output on the collocation points, `θ ↦ 𝓛u(x_r^j, θ)`. -/
def opOutputs {d Nr : ℕ} (Lop : ((Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ)
    (u : (Fin d → ℝ) → (P → ℝ) → ℝ) (xr : Fin Nr → Fin d → ℝ) : Fin Nr → (P → ℝ) → ℝ :=
  fun j θ => opOutput Lop u (xr j) θ

end General

/-! ### The one-hidden-layer network of Section 4 -/

/-- Section 4, eq. (4.2): index set of the parameters `θ = (W^(0), W^(1), b^(0), b^(1))` of a
network of width `N`: `(0, k) ↦ W^(0)_k`, `(1, k) ↦ W^(1)_k`, `(2, k) ↦ b^(0)_k`, and the single
output bias `b^(1)`. -/
abbrev PIdx (N : ℕ) := (Fin 3 × Fin N) ⊕ Unit

/-- Index of the first-layer weight `W^(0)_k`. -/
def idxW0 {N : ℕ} (k : Fin N) : PIdx N := Sum.inl (0, k)

/-- Index of the output weight `W^(1)_k`. -/
def idxW1 {N : ℕ} (k : Fin N) : PIdx N := Sum.inl (1, k)

/-- Index of the hidden bias `b^(0)_k`. -/
def idxB0 {N : ℕ} (k : Fin N) : PIdx N := Sum.inl (2, k)

/-- Index of the output bias `b^(1)`. -/
def idxB1 {N : ℕ} : PIdx N := Sum.inr ()

/-- Eq. (4.2): the one-hidden-layer network in NTK parameterization,
`u(x, θ) = N^{-1/2} ∑_k W^(1)_k σ(W^(0)_k x + b^(0)_k) + b^(1)`. -/
def netU (σ : ℝ → ℝ) {N : ℕ} (θ : PIdx N → ℝ) (x : ℝ) : ℝ :=
  (1 / Real.sqrt N) * ∑ k, θ (idxW1 k) * σ (θ (idxW0 k) * x + θ (idxB0 k)) + θ idxB1

/-- Eq. (4.3): `u_xx(x, θ)`, the second derivative in `x` of the network `x ↦ u(x, θ)`. -/
def netUxx (σ : ℝ → ℝ) {N : ℕ} (θ : PIdx N → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv (fun y => netU σ θ y)) x

/-- Section 4: the initialization, all weights and biases i.i.d. `𝒩(0, 1)`. -/
def initMeasure (N : ℕ) : Measure (PIdx N → ℝ) :=
  Measure.pi (fun _ : PIdx N => gaussianReal 0 1)

/-- `E_{w, b ∼ 𝒩(0,1)} F(w, b)` for independent standard Gaussians `w, b`. -/
def gaussE (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, F z.1 z.2 ∂((gaussianReal 0 1).prod (gaussianReal 0 1))

/-- Eq. (2.4) with `h = 1`: `Σ^(1)(x, x') = E_{(u,v) ∼ 𝒩(0, Λ^(1))}[σ(u)σ(v)] + 1`, where `Λ^(1)` is
built from `Σ^(0)(x, x') = x x' + 1`. Here `(u, v) = (w x + b, w x' + b)` with `w, b ∼ 𝒩(0,1)`
independent, which has covariance `Λ^(1)`. -/
def sigma1 (σ : ℝ → ℝ) (x x' : ℝ) : ℝ :=
  gaussE (fun w b => σ (w * x + b) * σ (w * x' + b)) + 1

/-- Eq. (2.5) with `h = 1`: `Σ̇^(1)(x, x') = E_{(u,v) ∼ 𝒩(0, Λ^(1))}[σ̇(u)σ̇(v)]`, written with
`(u, v) = (w x + b, w x' + b)`. -/
def sigmaDot1 (σ : ℝ → ℝ) (x x' : ℝ) : ℝ :=
  gaussE (fun w b => deriv σ (w * x + b) * deriv σ (w * x' + b))

/-- Theorem 4.1, eq. (4.6): `Σ_xx^(1)(x, x') = E_{u,v ∼ 𝒩(0,1)}[u⁴ σ̈(ux + v) σ̈(ux' + v)]`. -/
def sigmaXX (σ : ℝ → ℝ) (x x' : ℝ) : ℝ :=
  gaussE (fun u v => u ^ 4 * iteratedDeriv 2 σ (u * x + v) * iteratedDeriv 2 σ (u * x' + v))

/-- Appendix C: the limit `Θ_uu^(1)(x, x')` of `K_uu(0)`, as the law-of-large-numbers steps of the
proof give it: `Σ̇^(1)(x,x') x x' + E[σ(wx+b)σ(wx'+b)] + Σ̇^(1)(x,x') + 1`. -/
def thetaUU (σ : ℝ → ℝ) (x x' : ℝ) : ℝ :=
  sigmaDot1 σ x x' * (x * x') + gaussE (fun w b => σ (w * x + b) * σ (w * x' + b)) +
    sigmaDot1 σ x x' + 1

/-- Appendix C: the limit `Θ_ur^(1)(x, x') = A_ur + B_ur + C_ur` of `K_ur(0)` between a boundary
input `x` and a collocation input `x'`, with the expectations the law of large numbers gives
(`w, b ∼ 𝒩(0,1)`, `σ^(k)` evaluated at `w x + b` or `w x' + b`). -/
def thetaUR (σ : ℝ → ℝ) (x x' : ℝ) : ℝ :=
  gaussE (fun w b => w ^ 2 * deriv σ (w * x + b) * iteratedDeriv 3 σ (w * x' + b)) * (x * x') +
    2 * gaussE (fun w b => w * deriv σ (w * x + b) * iteratedDeriv 2 σ (w * x' + b)) * x +
    gaussE (fun w b => w ^ 2 * σ (w * x + b) * iteratedDeriv 2 σ (w * x' + b)) +
    gaussE (fun w b => w ^ 2 * deriv σ (w * x + b) * iteratedDeriv 3 σ (w * x' + b))

/-- Appendix C: the limit `Θ_rr^(1)(x, x') = A_rr + B_rr + C_rr` of `K_rr(0)`, with the
expectations the law of large numbers gives. -/
def thetaRR (σ : ℝ → ℝ) (x x' : ℝ) : ℝ :=
  gaussE (fun w b => w ^ 4 * iteratedDeriv 3 σ (w * x + b) * iteratedDeriv 3 σ (w * x' + b)) *
      (x * x') +
    2 * gaussE (fun w b => w ^ 3 * iteratedDeriv 3 σ (w * x + b) *
      iteratedDeriv 2 σ (w * x' + b)) * x +
    2 * gaussE (fun w b => w ^ 3 * iteratedDeriv 3 σ (w * x' + b) *
      iteratedDeriv 2 σ (w * x + b)) * x' +
    4 * gaussE (fun w b => w ^ 2 * iteratedDeriv 2 σ (w * x + b) *
      iteratedDeriv 2 σ (w * x' + b)) +
    gaussE (fun w b => w ^ 4 * iteratedDeriv 2 σ (w * x + b) * iteratedDeriv 2 σ (w * x' + b)) +
    gaussE (fun w b => w ^ 4 * iteratedDeriv 3 σ (w * x + b) * iteratedDeriv 3 σ (w * x' + b))

/-- Section 4, eq. (4.1): training data of the model problem `u_xx = f` on `Ω = (a, b)`,
`u = g` on `∂Ω = {a, b}`: boundary points `x_b^i ∈ ∂Ω` and collocation points `x_r^j ∈ Ω`. -/
def IsModelData {Nb Nr : ℕ} (a b : ℝ) (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) : Prop :=
  a < b ∧ (∀ i, xb i = a ∨ xb i = b) ∧ ∀ j, xr j ∈ Set.Ioo a b

/-- Section 4: the boundary outputs `θ ↦ u(x_b^i, θ)` of the one-hidden-layer network. -/
def modelU (σ : ℝ → ℝ) {N Nb : ℕ} (xb : Fin Nb → ℝ) : Fin Nb → (PIdx N → ℝ) → ℝ :=
  fun i θ => netU σ θ (xb i)

/-- Section 4: the residual outputs `θ ↦ u_xx(x_r^j, θ)` of the one-hidden-layer network. -/
def modelR (σ : ℝ → ℝ) {N Nr : ℕ} (xr : Fin Nr → ℝ) : Fin Nr → (PIdx N → ℝ) → ℝ :=
  fun j θ => netUxx σ θ (xr j)

/-- Eq. (3.4) for the model problem (4.1):
`L(θ) = ½ ∑ᵢ |u(x_b^i, θ) - g(x_b^i)|² + ½ ∑ⱼ |u_xx(x_r^j, θ) - f(x_r^j)|²`. -/
def modelLoss (σ : ℝ → ℝ) {N Nb Nr : ℕ} (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (g f : ℝ → ℝ) :
    (PIdx N → ℝ) → ℝ :=
  pinnLoss (modelU σ xb) (modelR σ xr) (fun i => g (xb i)) (fun j => f (xr j))

/-- Theorem 4.3: the NTK `K(θ)` of the one-hidden-layer PINN for the model problem (eq. (3.9)). -/
def modelNTK (σ : ℝ → ℝ) {N Nb Nr : ℕ} (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (θ : PIdx N → ℝ) :
    Matrix (Fin Nb ⊕ Fin Nr) (Fin Nb ⊕ Fin Nr) ℝ :=
  pinnNTK (modelU σ xb) (modelR σ xr) θ

/-- Theorem 4.3 and Appendix C: the limiting kernel
`K* = [[Θ_uu, Θ_ur], [Θ_ru, Θ_rr]]` on the training data, with `Θ_ru(x, x') = Θ_ur(x', x)`. -/
def limitNTK (σ : ℝ → ℝ) {Nb Nr : ℕ} (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) :
    Matrix (Fin Nb ⊕ Fin Nr) (Fin Nb ⊕ Fin Nr) ℝ :=
  Matrix.fromBlocks (Matrix.of fun i j => thetaUU σ (xb i) (xb j))
    (Matrix.of fun i j => thetaUR σ (xb i) (xr j))
    (Matrix.of fun i j => thetaUR σ (xb j) (xr i))
    (Matrix.of fun i j => thetaRR σ (xr i) (xr j))

/-- Theorem 4.1: `γ` is the centred Gaussian law `𝒩(0, C)` on `ℝⁿ`, characterised by its
characteristic function `∫ e^{i⟨t, y⟩} dγ(y) = e^{-tᵀ C t / 2}`. -/
def IsCenteredGaussian {n : ℕ} (γ : Measure (Fin n → ℝ)) (C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsProbabilityMeasure γ ∧
    ∀ t : Fin n → ℝ, ∫ y, Complex.exp (Complex.I * ((∑ i, t i * y i : ℝ) : ℂ)) ∂γ =
      Complex.exp (-(1 / 2 : ℂ) * ((∑ i, ∑ j, t i * t j * C i j : ℝ) : ℂ))

/-- Theorem 4.4 (iii): `σ` is smooth and `|σ^(k)| ≤ C` for `k = 0, 1, 2, 3, 4`. -/
def ActivationBounded4 (σ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ σ ∧ ∃ C > 0, ∀ k ≤ 4, ∀ z, |iteratedDeriv k σ z| ≤ C

/-- Theorem 4.4 (i): for a family of training trajectories `θ_N(t)`, one per width `N`, all
parameters are bounded on `[0, T]`, `sup_{t ∈ [0,T]} ‖θ_N(t)‖_∞ ≤ C`, with `C` independent of `N`. -/
def ParamsUnifBounded (T : ℝ) (θ : (N : ℕ) → ℝ → PIdx N → ℝ) : Prop :=
  ∃ C > 0, ∀ N, ∀ t ∈ Set.Icc 0 T, ∀ p, |θ N t p| ≤ C

/-- Theorem 4.4 (ii), as printed: `∫_0^T |∑ᵢ (u(x_b^i, θ(τ)) - g(x_b^i))| dτ ≤ C` and
`∫_0^T |∑ⱼ (u_xx(x_r^j, θ(τ)) - f(x_r^j))| dτ ≤ C`, with `C` independent of `N`. -/
def ResidualSumBound (σ : ℝ → ℝ) {Nb Nr : ℕ} (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ) (g f : ℝ → ℝ)
    (T : ℝ) (θ : (N : ℕ) → ℝ → PIdx N → ℝ) : Prop :=
  ∃ C > 0, ∀ N,
    (∫ τ in (0 : ℝ)..T, |∑ i, (netU σ (θ N τ) (xb i) - g (xb i))|) ≤ C ∧
    (∫ τ in (0 : ℝ)..T, |∑ j, (netUxx σ (θ N τ) (xr j) - f (xr j))|) ≤ C

/-- Theorem 4.4 (ii) in the form its proof (Lemma D.2) uses: the absolute value is inside the sum,
`∫_0^T ∑ᵢ |u(x_b^i, θ(τ)) - g(x_b^i)| dτ ≤ C` and `∫_0^T ∑ⱼ |u_xx(x_r^j, θ(τ)) - f(x_r^j)| dτ ≤ C`,
with `C` independent of `N`. -/
def ResidualAbsSumBound (σ : ℝ → ℝ) {Nb Nr : ℕ} (xb : Fin Nb → ℝ) (xr : Fin Nr → ℝ)
    (g f : ℝ → ℝ) (T : ℝ) (θ : (N : ℕ) → ℝ → PIdx N → ℝ) : Prop :=
  ∃ C > 0, ∀ N,
    (∫ τ in (0 : ℝ)..T, ∑ i, |netU σ (θ N τ) (xb i) - g (xb i)|) ≤ C ∧
    (∫ τ in (0 : ℝ)..T, ∑ j, |netUxx σ (θ N τ) (xr j) - f (xr j)|) ≤ C

end PINNNeuralTangent


