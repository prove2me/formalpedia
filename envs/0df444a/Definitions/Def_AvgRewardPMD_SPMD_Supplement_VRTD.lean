-- Prove2me | Definitions.Def_AvgRewardPMD_SPMD_Supplement_VRTD
-- name    : AvgRewardPMD_SPMD_Supplement_VRTD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:24:35.622897+00:00
-- url     : https://prove2.me/theorems/90af8900-cb35-4e04-ad15-7412bf8cb091
-- title:
--   §4.2.1, pp. 19–20, 35–36 — D-norm, g (4.9), g̃ (4.10), 1−β (4.11), B, μ, Φ, M (4.8), Q̄* (4.7), Σ̄, W₁, C_M, C_R, C_max, Markovian trajectory, Algorithm 3 (VRTD)
-- statement:
--   The objects of the variance-reduced temporal difference (VRTD) method of §4.2.1 (Li, Wu and Lan, pp. 19–21, with the constants of Appendix A.4, pp. 35–36).
--
--   Fix a policy $\pi$, write $P=P^\pi$ for the state–action transition matrix $P((s,a),(s',a'))=\mathsf P(s'\mid s,a)\pi(a'\mid s')$, $\nu=\nu^\pi$ for a stationary distribution of $P_\pi$, and $D=\mathrm{diag}(\nu(s)\pi(a\mid s))$. The features are the columns $\psi_1,\dots,\psi_d$ of $\Psi\in\mathbb R^{(|\mathcal S||\mathcal A|)\times d}$, with feature vectors $\psi(s,a)=(\psi_i(s,a))_i$ and feature subspace $\mathcal S=\mathrm{span}\{\psi_1,\dots,\psi_d\}$. Here $c(s,a)$ is the overall cost of §4 (the cost plus $h^\pi(s)$).
--
--   1. **Norm and quadratic form.** $\|x\|_D^2=\sum_{(s,a)}\nu(s)\pi(a\mid s)x(s,a)^2$ and $x^\top D(I-P)x$.
--   2. **Modulus (4.11).** $1-\beta:=\inf_{x\in\mathcal S,\ \|x\|_D=1}x^\top D(I-P)x$.
--   3. **Operators (4.9)–(4.10).** $g(\theta,\rho)=\Psi^\top D(\Psi\theta-P\Psi\theta-c+\rho\mathbf 1)$ and, at a sample $\xi=\{(s,a),(s',a'),c(s,a)\}$, $\tilde g(\theta,\rho,\xi)=\big(\langle\psi(s,a)-\psi(s',a'),\theta\rangle-c(s,a)+\rho\big)\psi(s,a)$.
--   4. **Geometry (4.8).** $B=\Psi^\top D\Psi$, $\mu=\lambda_{\min}(B)$, $\Phi=\Psi B^{-1/2}$, $M=\Phi^\top DP\Phi$.
--   5. **Aligned differential Q-function (4.7).** $\bar Q^*=\bar Q^\pi+\hat b\mathbf 1$ with $\hat b=\arg\min_b\|\bar Q^\pi+b\mathbf 1-\Psi\theta^*\|_D$.
--   6. **Covariance and $W_1$ (Theorem 4).** $\bar\Sigma=\mathrm{cov}\big[B^{-1/2}(\langle\psi(s,a)-\psi(s',a'),\theta^*\rangle-c(s,a))\psi(s,a)\big]$ for $s\sim\nu$, $a\sim\pi(\cdot\mid s)$, $s'\sim\mathsf P(\cdot\mid s,a)$, $a'\sim\pi(\cdot\mid s')$, and
--   $$W_1=22\,\mathrm{trace}\{(I_d-M)^{-1}\bar\Sigma(I_d-M)^{-\top}\}+\frac{4}{\mu(1-\beta)^2}\|\bar Q^*-\Psi\theta^*\|_D^2 .$$
--   7. **Mixing constants (pp. 35–36).** For a constant $C_P$, $C_M=\dfrac{C_P}{\sqrt{\min_{s,a}\nu(s)\pi(a\mid s)}}\|\Psi\|_2\|I-P\|_2$, $C_R=C_P\|\Psi\|_2$, $C_{\max}=\max\{C_P,C_M,C_R\}$, with $\|\cdot\|_2$ the spectral norm.
--   8. **Markovian trajectory (§2.2, p. 7).** A sequence $(s_0,a_0),(s_1,a_1),\dots$ is a trajectory of the chain $P$ from an arbitrary initial law when $\Pr(X_0=x_0,\dots,X_n=x_n)=\Pr(X_0=x_0)\prod_{i<n}P(x_i,x_{i+1})$ for all $n$ and all $x_0,\dots,x_n$.
--   9. **Algorithm 3 (VRTD, p. 20).** From an input $\hat\theta_0$, epoch $k=1,\dots,K$ sets $\theta_1=\tilde\theta=\hat\theta_{k-1}$; reads $N'_k$ state–action samples from the trajectory, each the last of $\tau'+1$ successive ones, and sets $\tilde\rho$ to the average of their costs; reads $N_k$ transition samples, each the last of $\tau'+1$ successive ones, and sets $\hat g(\tilde\theta,\tilde\rho)$ to the average of $\tilde g(\tilde\theta,\tilde\rho,\cdot)$; then for $t=1,\dots,T$ reads a transition sample $\xi_t(\tau)$, the last of $\tau+1$ successive ones, and sets
--   $$\theta_{t+1}=\theta_t-\eta\big[\tilde g(\theta_t,\tilde\rho,\xi_t(\tau))-\tilde g(\tilde\theta,\tilde\rho,\xi_t(\tau))+\hat g(\tilde\theta,\tilde\rho)\big];$$
--   its outputs are $\hat\theta_k=\frac1T\sum_{t=1}^T\theta_t$ and $\hat\rho_k=\tilde\rho$. The trajectory is consumed in this order, epoch after epoch, without restarting.
--
--   These are the objects of Lemma 8 and Theorem 4: the modulus $1-\beta$ replaces the effective horizon of discounted problems, and $W_1$ collects the stochastic error of VRTD.
--
--   **Formalization Note** $\mathcal S$ is $\{\Psi\theta:\theta\in\mathbb R^d\}$; $1-\beta$ and $\mu$ are real infima (`sInf`) over sets that are nonempty and bounded below when $d\ge1$ (for $\mu$ the Rayleigh quotient over the unit sphere, whose minimum is $\lambda_{\min}(B)$ for symmetric $B$). $B^{-1/2}$ is the continuous functional calculus of $B$ with $x\mapsto x^{-1/2}$; $\|\cdot\|_2$ is the operator norm of `Matrix.toEuclideanLin`; matrix inverses are Mathlib's `⁻¹` (the paper's Lemma 13 shows $I_d-M$ invertible). $\hat b$ is written in its closed form $\langle\Psi\theta^*-\bar Q^\pi,\mathbf 1\rangle_D/\langle\mathbf 1,\mathbf 1\rangle_D$, the unique minimizer. The covariance is $\mathbb E[ZZ^\top]-\mathbb E[Z]\mathbb E[Z]^\top$ under the stationary quadruple law, a finite sum. In the trajectory, the transition sample with last index $j$ is $((s_j,a_j),(s_{j+1},a_{j+1}),c(s_j,a_j))$; within an epoch starting at position $b$, the $i$-th cost sample ($i=0,\dots,N'_k-1$) is at position $b+i(\tau'+1)+\tau'$, the $i$-th recentering sample at $b+(\tau'+1)N'_k+i(\tau'+1)+\tau'$, the $t$-th inner sample ($t=0,\dots,T-1$) at $b+(\tau'+1)(N'_k+N_k)+t(\tau+1)+\tau$, and epoch $k+1$ starts $(\tau'+1)(N'_k+N_k)+(\tau+1)T$ positions later.
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, pp. 19–20 (D, ψ, 𝒮, (4.6)–(4.11), Algorithm 3), p. 21 (W₁, Σ̄), pp. 35–36 (C_M Lemma 11, C_R Lemma 12, C_max), p. 7 (Markovian noise model)

import Mathlib
import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD.Supplement

open FoundationsML.ReinforcementLearning MeasureTheory Matrix

noncomputable section

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-! ### Stationary feature geometry of §4.2.1 (pp. 19–20)

A fixed policy `π` is evaluated; `P = P^π` is the state–action matrix `saTransition P π`,
`ν = ν^π` a stationary distribution of `P_π`, and `D = diag(ν(s) π(a|s))`. Features are the
columns `ψ_1, …, ψ_d` of `Ψ : Matrix (S × A) (Fin d) ℝ`, and `ψ(s,a) = (Ψ (s,a) i)_i`. -/

/-- The diagonal of the weighting matrix `D = D^π` (p. 19): `D((s,a),(s,a)) = ν(s) π(a|s)`. -/
def saWeight (ν : S → ℝ) (π : S → A → ℝ) : S × A → ℝ := fun x => ν x.1 * π x.1 x.2

/-- The squared weighted norm `‖x‖²_D = ∑_{(s,a)} ν(s) π(a|s) x(s,a)²`. -/
def dNormSq (ν : S → ℝ) (π : S → A → ℝ) (x : S × A → ℝ) : ℝ :=
  ∑ y, saWeight ν π y * x y ^ 2

/-- The quadratic form `xᵀ D (I − P) x` on `ℝ^{|S||A|}` (4.11), with `P = P^π`. -/
def dirichletForm (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) (x : S × A → ℝ) : ℝ :=
  ∑ y, saWeight ν π y * x y * (x y - (saTransition P π *ᵥ x) y)

/-- The constant `1 − β := inf_{x ∈ 𝒮, ‖x‖_D = 1} xᵀ D (I − P) x` of (4.11), p. 20, where
`𝒮 = span{ψ_1, …, ψ_d} = {Ψ θ : θ ∈ ℝ^d}` is the feature subspace. -/
def dirichletGap (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) {d : ℕ}
    (Ψ : Matrix (S × A) (Fin d) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ θ : Fin d → ℝ, dNormSq ν π (Ψ *ᵥ θ) = 1 ∧ r = dirichletForm P π ν (Ψ *ᵥ θ)}

/-- The deterministic operator (4.9), p. 19: `g(θ, ρ) = Ψᵀ D (Ψθ − PΨθ − c + ρ 1)`. -/
def opG (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) (c : S → A → ℝ) {d : ℕ}
    (Ψ : Matrix (S × A) (Fin d) ℝ) (θ : Fin d → ℝ) (ρ : ℝ) : Fin d → ℝ :=
  Ψᵀ *ᵥ (fun y => saWeight ν π y *
    ((Ψ *ᵥ θ) y - (saTransition P π *ᵥ (Ψ *ᵥ θ)) y - c y.1 y.2 + ρ))

/-- The stochastic operator (4.10), p. 19, at a sample `ξ = {(s,a), (s',a'), c(s,a)}`:
`g̃(θ, ρ, ξ) = (⟨ψ(s,a) − ψ(s',a'), θ⟩ − c(s,a) + ρ) ψ(s,a)`. -/
def gTilde (c : S → A → ℝ) {d : ℕ} (Ψ : Matrix (S × A) (Fin d) ℝ) (θ : Fin d → ℝ) (ρ : ℝ)
    (x x' : S × A) : Fin d → ℝ :=
  (∑ i, (Ψ x i - Ψ x' i) * θ i - c x.1 x.2 + ρ) • (fun i => Ψ x i)

/-- The Gram matrix `B = Ψᵀ D Ψ`, `B_{ij} = ⟨ψ_i, ψ_j⟩_D` (p. 19). -/
def gram (ν : S → ℝ) (π : S → A → ℝ) {d : ℕ} (Ψ : Matrix (S × A) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Ψᵀ * diagonal (saWeight ν π) * Ψ

/-- `μ := λ_min(B)` of (4.8), p. 19, as the minimum of the Rayleigh quotient of the symmetric
matrix `B` over the unit sphere of `ℝ^d`. -/
def minEig {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ θ : Fin d → ℝ, ∑ i, θ i ^ 2 = 1 ∧ r = θ ⬝ᵥ (B *ᵥ θ)}

/-- The inverse square root `B^{-1/2}` (p. 19), by the continuous functional calculus of the
real symmetric matrix `B`. -/
def invSqrt {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) B

/-- `Φ := Ψ B^{-1/2}` (p. 19). -/
def featPhi (ν : S → ℝ) (π : S → A → ℝ) {d : ℕ} (Ψ : Matrix (S × A) (Fin d) ℝ) :
    Matrix (S × A) (Fin d) ℝ :=
  Ψ * invSqrt (gram ν π Ψ)

/-- `M := Φᵀ D P Φ` of (4.8), p. 19. -/
def matM (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) {d : ℕ}
    (Ψ : Matrix (S × A) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (featPhi ν π Ψ)ᵀ * diagonal (saWeight ν π) * saTransition P π * featPhi ν π Ψ

/-- The spectral norm `‖A‖₂` (operator norm `ℓ₂ → ℓ₂`) of a real matrix. -/
def opNorm2 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-- `C_M := C_P ‖Ψ‖₂ ‖I − P‖₂ / √(min_{s,a} ν(s) π(a|s))` (Lemma 11, p. 35). -/
def constCM (CP : ℝ) (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) {d : ℕ}
    (Ψ : Matrix (S × A) (Fin d) ℝ) : ℝ :=
  CP / Real.sqrt (⨅ x, saWeight ν π x) * opNorm2 Ψ * opNorm2 (1 - saTransition P π)

/-- `C_R := C_P ‖Ψ‖₂` (Lemma 12, p. 36). -/
def constCR (CP : ℝ) {d : ℕ} (Ψ : Matrix (S × A) (Fin d) ℝ) : ℝ :=
  CP * opNorm2 Ψ

/-- `C_max := max{C_P, C_M, C_R}` (p. 36). -/
def constCmax (CP : ℝ) (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) {d : ℕ}
    (Ψ : Matrix (S × A) (Fin d) ℝ) : ℝ :=
  max CP (max (constCM CP P π ν Ψ) (constCR CP Ψ))

/-- `Q̄* = Q̄^π + b̂ 1` of (4.7), p. 19, where `b̂ = argmin_b ‖Q̄^π + b 1 − Ψθ*‖_D`; the minimizer
is `b̂ = ⟨Ψθ* − Q̄^π, 1⟩_D / ⟨1, 1⟩_D` (unique since `⟨1,1⟩_D > 0`). `Q̄^π = diffQ P π c`. -/
def alignedQ (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) (c : S → A → ℝ) {d : ℕ}
    (Ψ : Matrix (S × A) (Fin d) ℝ) (θstar : Fin d → ℝ) : S × A → ℝ :=
  let bhat := (∑ y, saWeight ν π y * ((Ψ *ᵥ θstar) y - diffQ P π c y)) / ∑ y, saWeight ν π y
  fun x => diffQ P π c x + bhat

/-- The covariance `Σ̄ := cov[B^{-1/2}(⟨ψ(s,a) − ψ(s',a'), θ*⟩ − c(s,a)) ψ(s,a)]` (Theorem 4,
p. 21) for `s ∼ ν, a ∼ π(·|s), s' ∼ P(·|s,a), a' ∼ π(·|s')`, i.e. under the weights
`ν(s) π(a|s) P(s'|s,a) π(a'|s')` on pairs `((s,a),(s',a'))`: `E[Z Zᵀ] − E[Z] E[Z]ᵀ`. -/
def covSigma (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) (c : S → A → ℝ) {d : ℕ}
    (Ψ : Matrix (S × A) (Fin d) ℝ) (θstar : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  let w : (S × A) × (S × A) → ℝ := fun z => saWeight ν π z.1 * saTransition P π z.1 z.2
  let Z : (S × A) × (S × A) → Fin d → ℝ := fun z =>
    invSqrt (gram ν π Ψ) *ᵥ
      ((∑ i, (Ψ z.1 i - Ψ z.2 i) * θstar i - c z.1.1 z.1.2) • (fun i => Ψ z.1 i))
  let m : Fin d → ℝ := ∑ z, w z • Z z
  (∑ z, w z • vecMulVec (Z z) (Z z)) - vecMulVec m m

/-- `W₁ := 22 trace{(I_d − M)^{-1} Σ̄ (I_d − M)^{-⊤}} + 4/(μ(1−β)²) ‖Q̄* − Ψθ*‖²_D`
(Theorem 4, p. 21). -/
def constW1 (P : S → A → S → ℝ) (π : S → A → ℝ) (ν : S → ℝ) (c : S → A → ℝ) {d : ℕ}
    (Ψ : Matrix (S × A) (Fin d) ℝ) (θstar : Fin d → ℝ) : ℝ :=
  let Minv := (1 - matM P π ν Ψ)⁻¹
  22 * trace (Minv * covSigma P π ν c Ψ θstar * Minvᵀ)
    + 4 / (minEig (gram ν π Ψ) * dirichletGap P π ν Ψ ^ 2)
      * dNormSq ν π (fun x => alignedQ P π ν c Ψ θstar x - (Ψ *ᵥ θstar) x)

/-! ### The Markovian noise model (§2.2, p. 7) -/

/-- `X` is a single trajectory `(s_0,a_0), (s_1,a_1), …` of the state–action Markov chain with
transition matrix `P^π((s,a),(s',a')) = P(s'|s,a) π(a'|s')`, from an arbitrary initial law:
the events `{X_n = x}` are measurable, and for every `n` and every path `x`,
`P(X_0 = x_0, …, X_n = x_n) = P(X_0 = x_0) ∏_{i<n} P^π(x_i, x_{i+1})`. -/
def IsSAMarkovChain {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω)
    (P : S → A → S → ℝ) (π : S → A → ℝ) (X : ℕ → Ω → S × A) : Prop :=
  (∀ n x, MeasurableSet {ω | X n ω = x}) ∧
  ∀ (n : ℕ) (x : ℕ → S × A),
    μ {ω | ∀ i ≤ n, X i ω = x i}
      = μ {ω | X 0 ω = x 0} *
          ∏ i ∈ Finset.range n, ENNReal.ofReal (saTransition P π (x i) (x (i + 1)))

/-! ### Algorithm 3 (VRTD), p. 20

The trajectory is consumed in order. Epoch `k` (`k = 1, …, K`) starts at position
`epochStart k` and uses, in order: `N'_k` state–action samples, the `i`-th (`i = 0, …, N'_k − 1`)
being the last of `τ' + 1` successive ones (position `start + i(τ'+1) + τ'`); then `N_k`
transition samples `ξ = ((s_j,a_j),(s_{j+1},a_{j+1}), c(s_j,a_j))`, each the last of `τ' + 1`
successive transition samples; then `T` transition samples, each the last of `τ + 1` successive
ones. -/

/-- The number of trajectory positions consumed by epoch `k`. -/
def epochLength (τ τ' T : ℕ) (N N' : ℕ → ℕ) (k : ℕ) : ℕ :=
  (τ' + 1) * (N' k + N k) + (τ + 1) * T

/-- The first trajectory position used by epoch `k ≥ 1` (epochs `1, …, k − 1` come first). -/
def epochStart (τ τ' T : ℕ) (N N' : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico 1 k, epochLength τ τ' T N N' j

/-- One VRTD epoch (lines 3–10 of Algorithm 3) started at trajectory position `start`, with
`n = N_k`, `n' = N'_k` and recentering point `θ̃ = θprev = θ̂_{k−1}`. Returns `(θ̂_k, ρ̂_k)`:
`ρ̃ = (1/N'_k) ∑ c(s̃_i, ã_i)`, `ĝ(θ̃, ρ̃) = (1/N_k) ∑ g̃(θ̃, ρ̃, ξ^k_i(τ'))`, `θ_1 = θ̃`,
`θ_{t+1} = θ_t − η[g̃(θ_t, ρ̃, ξ_t(τ)) − g̃(θ̃, ρ̃, ξ_t(τ)) + ĝ(θ̃, ρ̃)]`, and
`θ̂_k = (1/T) ∑_{t=1}^T θ_t`, `ρ̂_k = ρ̃`. -/
def vrtdEpoch (c : S → A → ℝ) {d : ℕ} (Ψ : Matrix (S × A) (Fin d) ℝ) (η : ℝ)
    (τ τ' T n n' start : ℕ) (path : ℕ → S × A) (θprev : Fin d → ℝ) : (Fin d → ℝ) × ℝ :=
  let ρt : ℝ := (n' : ℝ)⁻¹ * ∑ i ∈ Finset.range n',
    c (path (start + i * (τ' + 1) + τ')).1 (path (start + i * (τ' + 1) + τ')).2
  let j₀ := start + (τ' + 1) * n'
  let gh : Fin d → ℝ := (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n,
    gTilde c Ψ θprev ρt (path (j₀ + i * (τ' + 1) + τ')) (path (j₀ + i * (τ' + 1) + τ' + 1))
  let j₁ := start + (τ' + 1) * (n' + n)
  -- `inner t = θ_{t+1}`; the sample `ξ_{t+1}(τ)` sits at position `j₁ + t(τ+1) + τ` (0-based `t`).
  let inner : ℕ → Fin d → ℝ := fun t => Nat.rec θprev (fun t θt => θt - η •
      (gTilde c Ψ θt ρt (path (j₁ + t * (τ + 1) + τ))
          (path (j₁ + t * (τ + 1) + τ + 1))
        - gTilde c Ψ θprev ρt (path (j₁ + t * (τ + 1) + τ))
          (path (j₁ + t * (τ + 1) + τ + 1))
        + gh)) t
  ((T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, inner t, ρt)

/-- The VRTD outputs `(θ̂_k, ρ̂_k)` after `k` epochs along the trajectory `path`, from the input
`θ̂_0 = θ0` (`ρ̂_0 := 0` is unused). -/
def vrtd (c : S → A → ℝ) {d : ℕ} (Ψ : Matrix (S × A) (Fin d) ℝ) (η : ℝ) (τ τ' T : ℕ)
    (N N' : ℕ → ℕ) (θ0 : Fin d → ℝ) (path : ℕ → S × A) : ℕ → (Fin d → ℝ) × ℝ
  | 0 => (θ0, 0)
  | k + 1 => vrtdEpoch c Ψ η τ τ' T (N (k + 1)) (N' (k + 1))
      (epochStart τ τ' T N N' (k + 1)) path (vrtd c Ψ η τ τ' T N N' θ0 path k).1

end

end AvgRewardPMD.SPMD.Supplement


