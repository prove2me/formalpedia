-- Prove2me | Definitions.Def_DeepMFC_FiniteHorizon_Networks
-- name    : DeepMFC_FiniteHorizon_Networks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:49.996372+00:00
-- url     : https://prove2.me/theorems/33013665-a0fb-48e5-90ae-c4f3c287e165
-- title:
--   §2.4, p. 4069 and §3.2, p. 4073 — periodic activations, one-hidden-layer networks 𝐍^ψ_{d+1,n_in,k} and the class 𝒞(R, K, L₁, L₂, L₃)
-- statement:
--   **Activation.** An activation function $\psi:\mathbb R\to\mathbb R$ is $2\pi$-periodic, of class $\mathcal C^3$, and has a nonzero first Fourier coefficient
--   $$\hat\psi_1=\int_{-\pi}^{\pi}\psi(x)e^{-ix}\,dx\ne0.$$
--
--   **Networks.** The layer functions $\mathbf L^\psi_{d_1,d_2}$ are the maps $\phi:\mathbb R^{d_1}\to\mathbb R^{d_2}$ with $\phi(x)_i=\psi(\beta_i+\sum_{j=1}^{d_1}w_{i,j}x_j)$ for some $\beta\in\mathbb R^{d_2}$ and $w\in\mathbb R^{d_2\times d_1}$; $\mathbf L_{d_1,d_2}$ is the same class with the identity activation. The one-hidden-layer networks are
--   $$\mathbf N^\psi_{d_0,n_{\rm in},d_2}=\{\phi_1\circ\phi_0:\ \phi_0\in\mathbf L^\psi_{d_0,n_{\rm in}},\ \phi_1\in\mathbf L_{n_{\rm in},d_2}\},$$
--   i.e. the case $\ell=1$ of (2.11). A network $\varphi:\mathbb R^{d+1}\to\mathbb R^k$ is used as a feedback function of $(t,x)\in\mathbb R\times\mathbb R^d$ through $(t,x)\mapsto\varphi(t,x)$.
--
--   **Lipschitz constants of a network.** For a feedback $u(t,x)$ and $K\ge0$, the Lipschitz constants of $u$, $\partial_xu$ and $\partial^2_{xx}u$, as functions of $(t,x)$ on $\mathbb R\times\mathbb R^d$, are at most $K$.
--
--   **The class $\mathcal C(R,K,L_1,L_2,L_3)$.** It consists of the functions $\mathfrak f:[0,T]\times\bar B_d(0,R)\to\mathbb R^k$ that are Lipschitz in $(t,x)$ with sup-norm at most $K$ and Lipschitz constant at most $L_1$, and are twice differentiable in $x$ with every $\partial_{x_i}\mathfrak f$ Lipschitz in $(t,x)$ with constant at most $L_2$ and every $\partial_{x_i,x_j}\mathfrak f$ Lipschitz in $(t,x)$ with constant at most $L_3$.
--
--   These are the neural networks over which the discrete problem is minimized, and the class of feedback functions they are shown to approximate together with two derivatives.
--
--   **Formalization Note.** Only the values of $\mathfrak f$ on $[0,T]\times\bar B_d(0,R)$ enter the class: the derivatives in $x$ are Fréchet derivatives within the closed ball, and every bound is required on that set. The derivatives $\partial_xu$, $\partial^2_{xx}u$ of a feedback are Fréchet derivatives in $x$ measured in operator norm; for a network, which is $\mathcal C^3$, they are the classical ones. Norms are sup norms; the Lipschitz conditions are for the max norm on $\mathbb R\times\mathbb R^d$, which changes constants only by dimensional factors. Only one hidden layer is defined, since Theorem 3 concerns $\mathbf N^\psi_{d+1,n_{\rm in},k}$.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4069, §2.4, (2.11); p. 4073, §3.2, the class 𝒞(R, K, L₁, L₂, L₃)

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

/-! # One-hidden-layer neural networks (§2.4, p. 4069) and the class `𝒞(R, K, L₁, L₂, L₃)` (§3.2,
p. 4073)

Carmona, Laurière, Ann. Appl. Probab. 32(6) (2022). -/

/-- The activation assumptions of §2.4: `ψ : ℝ → ℝ` is `2π`-periodic, of class `𝒞³`, and its first
Fourier coefficient `ψ̂₁ = ∫_{−π}^{π} ψ(x) e^{−ix} dx` is nonzero. -/
def IsActivation (ψ : ℝ → ℝ) : Prop :=
  Function.Periodic ψ (2 * Real.pi) ∧ ContDiff ℝ 3 ψ ∧
    (∫ x in (-Real.pi)..Real.pi, (ψ x : ℂ) * Complex.exp (-((x : ℂ) * Complex.I))) ≠ 0

/-- The layer functions `𝐋^ψ_{d₁,d₂}`: maps `ϕ : ℝ^{d₁} → ℝ^{d₂}` of the form
`ϕ(x)ᵢ = ψ(βᵢ + Σⱼ w_{i,j} xⱼ)` for some `β ∈ ℝ^{d₂}`, `w ∈ ℝ^{d₂×d₁}`. With `ψ = id` this is the
affine class `𝐋_{d₁,d₂}`. -/
def Layer (ψ : ℝ → ℝ) (d₁ d₂ : ℕ) : Set ((Fin d₁ → ℝ) → (Fin d₂ → ℝ)) :=
  {ϕ | ∃ (β : Fin d₂ → ℝ) (w : Matrix (Fin d₂) (Fin d₁) ℝ),
    ∀ x i, ϕ x i = ψ (β i + ∑ j, w i j * x j)}

/-- The one-hidden-layer networks `𝐍^ψ_{d₀,n_in,d₂}` ((2.11) with `ℓ = 1`): `φ = ϕ₁ ∘ ϕ₀` with
`ϕ₀ ∈ 𝐋^ψ_{d₀,n_in}` (hidden layer, activation `ψ`) and `ϕ₁ ∈ 𝐋_{n_in,d₂}` (identity output
activation). -/
def NN1 (ψ : ℝ → ℝ) (d₀ nin d₂ : ℕ) : Set ((Fin d₀ → ℝ) → (Fin d₂ → ℝ)) :=
  {φ | ∃ ϕ₀ ∈ Layer ψ d₀ nin, ∃ ϕ₁ ∈ Layer id nin d₂, φ = ϕ₁ ∘ ϕ₀}

/-- A network `φ : ℝ^{d+1} → ℝᵏ` used as a feedback function of `(t, x)`: `(t, x) ↦ φ(t, x)`. -/
def toFeedback {d k : ℕ} (φ : (Fin (d + 1) → ℝ) → (Fin k → ℝ)) : ℝ → E d → Fin k → ℝ :=
  fun t x => φ (Fin.cons t x)

/-- The Lipschitz constants of a feedback `u` (in practice a network), of `∂ₓu` and of `∂²ₓₓu`, as
functions of `(t, x)` on all of `ℝ × ℝᵈ`, are at most `K`. The derivatives are Fréchet derivatives
in `x` (operator norms). -/
def NetLip {d k : ℕ} (K : ℝ) (u : ℝ → E d → Fin k → ℝ) : Prop :=
  LipschitzWith (Real.toNNReal K) (fun p : ℝ × E d => u p.1 p.2) ∧
  LipschitzWith (Real.toNNReal K) (fun p : ℝ × E d => fderiv ℝ (u p.1) p.2) ∧
  LipschitzWith (Real.toNNReal K)
    (fun p : ℝ × E d => fderiv ℝ (fun x => fderiv ℝ (u p.1) x) p.2)

/-- The class `𝒞(R, K, L₁, L₂, L₃)` (p. 4073) of `𝔣 : [0, T] × B̄_d(0, R) → ℝᵏ`: `𝔣` is Lipschitz in
`(t, x)` with sup-norm at most `K` and Lipschitz constant at most `L₁`, and `𝔣` is twice
differentiable w.r.t. `x` such that every `∂_{xᵢ}𝔣` is Lipschitz in `(t, x)` with constant at most
`L₂` and every `∂_{xᵢ,xⱼ}𝔣` with constant at most `L₃`. Only the values on
`S = [0, T] × B̄_d(0, R)` matter; the `x`-derivatives are taken within the closed ball. -/
def InClassC {d k : ℕ} (T R K L₁ L₂ L₃ : ℝ) (𝔣 : ℝ → E d → Fin k → ℝ) : Prop :=
  (∀ t ∈ Set.Icc 0 T, ∀ x ∈ Metric.closedBall (0 : E d) R, ‖𝔣 t x‖ ≤ K) ∧
  LipschitzOnWith (Real.toNNReal L₁) (fun p : ℝ × E d => 𝔣 p.1 p.2)
    (Set.Icc 0 T ×ˢ Metric.closedBall 0 R) ∧
  ∃ (D1 : ℝ → E d → E d →L[ℝ] (Fin k → ℝ)) (D2 : ℝ → E d → E d →L[ℝ] E d →L[ℝ] (Fin k → ℝ)),
    (∀ t ∈ Set.Icc 0 T, ∀ x ∈ Metric.closedBall (0 : E d) R,
      HasFDerivWithinAt (𝔣 t) (D1 t x) (Metric.closedBall 0 R) x ∧
      HasFDerivWithinAt (D1 t) (D2 t x) (Metric.closedBall 0 R) x) ∧
    (∀ i : Fin d, LipschitzOnWith (Real.toNNReal L₂)
      (fun p : ℝ × E d => D1 p.1 p.2 (Pi.single i 1)) (Set.Icc 0 T ×ˢ Metric.closedBall 0 R)) ∧
    (∀ i j : Fin d, LipschitzOnWith (Real.toNNReal L₃)
      (fun p : ℝ × E d => D2 p.1 p.2 (Pi.single j 1) (Pi.single i 1))
      (Set.Icc 0 T ×ˢ Metric.closedBall 0 R))

end DeepMFC.FiniteHorizon


