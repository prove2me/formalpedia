-- Prove2me | Definitions.Def_ActorCritic_Finite_SteadyState
-- name    : ActorCritic_Finite_SteadyState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:36.393618+00:00
-- url     : https://prove2.me/theorems/7ff86700-ba6a-4c06-b6ac-65954b1734e9
-- title:
--   §§5–6 — T_θ, regenerative Q_θ, h̄(θ), Ḡ(θ) for TD(1) and TD(λ), R_k, H_θ, H̄(θ), r̄(θ), f(θ), e⁽¹⁾_k, e⁽²⁾_k
-- statement:
--   This module defines the objects of the critic and actor analysis of §§5–6, in the finite case, where every expectation is a finite sum or a series of matrix powers. Throughout, $\langle f,g\rangle_\theta=\sum_{x,u}\eta_\theta(x,u)f(x,u)g(x,u)$, extended entrywise to vector- and matrix-valued functions.
--
--   1. **Regeneration at $x^*$ (§5.1).** With $\tau=\min\{k>0\mid X_k=x^*\}$ for the chain under the fixed RSP $\theta$, $T_\theta(x,u)=\mathbf E_{\theta,x}[\tau\mid U_0=u]$ and $Q_\theta(x,u)=\mathbf E_{\theta,x}\big[\sum_{k=0}^{\tau-1}(c(X_k,U_k)-\bar\alpha(\theta))\mid U_0=u\big]$. With the taboo matrix $\tilde P_\theta((x,u),(y,\bar u))=p(y\mid x,u)\mu_\theta(\bar u\mid y)\,1\{y\ne x^*\}$ these are $T_\theta=\sum_{k\ge0}\tilde P_\theta^k\underline1$ and $Q_\theta=\sum_{k\ge0}\tilde P_\theta^k(c-\bar\alpha(\theta)\underline1)$.
--   2. **TD(1) steady-state quantities:** $\bar h_1(\theta)=\langle Q_\theta,\phi_\theta\rangle_\theta$, $\bar Z(\theta)=\langle T_\theta,\phi_\theta\rangle_\theta$, $\bar G_1(\theta)=\langle\phi_\theta,\phi_\theta'\rangle_\theta$.
--   3. **TD($\lambda$) steady-state quantities:**
--   $$
--   \bar h_1(\theta)=\sum_{k\ge0}\lambda^k\langle P_\theta^kc-\bar\alpha(\theta)\underline1,\phi_\theta\rangle_\theta,\qquad \bar G_1(\theta)=\langle\phi_\theta,\phi_\theta'\rangle_\theta-(1-\lambda)\sum_{k\ge0}\lambda^k\langle P_\theta^{k+1}\phi_\theta,\phi_\theta'\rangle_\theta,
--   $$
--   and $\bar Z(\theta)=(1-\lambda)^{-1}\langle\underline1,\phi_\theta\rangle_\theta$.
--   4. **Block forms.** For $L>0$, $\bar h(\theta)=\begin{pmatrix}L\bar\alpha(\theta)\\ \bar h_1(\theta)+\bar\alpha(\theta)\bar Z(\theta)\end{pmatrix}$, $\bar G(\theta)=\begin{pmatrix}1&0\\ \bar Z(\theta)/L&\bar G_1(\theta)\end{pmatrix}$ and $R_k=\begin{pmatrix}L\alpha_k\\ r_k\end{pmatrix}$.
--   5. **Actor objects (§6).** $H_\theta(x,u)=\psi_\theta(x,u)\phi_\theta'(x,u)$ ($n\times m$), $\bar H(\theta)=\langle\psi_\theta,\phi_\theta'\rangle_\theta$, $\bar r(\theta)$ the solution of $\bar h_1(\theta)=\bar G_1(\theta)\bar r(\theta)$, $f(\theta)=\bar H(\theta)\bar r(\theta)$, and along the algorithm
--   $$
--   e^{(1)}_k=\big(H_{\theta_k}(\hat X_{k+1},\hat U_{k+1})-\bar H(\theta_k)\big)r_k\Gamma(r_k),\qquad e^{(2)}_k=\bar H(\theta_k)\big(r_k\Gamma(r_k)-\bar r(\theta_k)\Gamma(\bar r(\theta_k))\big).
--   $$
--
--   These objects appear in the milestones of the mission (Lemmas 5.1–5.6, Theorem 5.7, Lemmas 6.1–6.2, (6.1)); the goal theorem does not use them.
--
--   **Formalization Note** The paper uses one letter $Q_\theta$ for three objects; here the regenerative one of §5.1 is `Qreg`, distinct from a general Poisson solution (`IsPoissonSol`). The series are Lean `tsum`s, which return $0$ for a divergent series; under Assumption 2.1(d) (for $T_\theta$, $Q_\theta$) and for $0<\lambda<1$ (for the TD($\lambda$) series, whose terms are bounded times $\lambda^k$) they converge. $\bar r(\theta)$ is $\bar G_1(\theta)^{-1}\bar h_1(\theta)$; under Assumptions 2.1 and 3.2, $\bar G_1(\theta)$ is positive definite (Lemmas 5.3, 5.6), so Lean's convention $A^{-1}=0$ for singular $A$ does not intervene. The $(i,j)$ entry of $\langle P_\theta^{k+1}\phi_\theta,\phi_\theta'\rangle_\theta$ is read as $\sum_{x,u}\eta_\theta(x,u)\phi^i_\theta(x,u)(P_\theta^{k+1}\phi^j_\theta)(x,u)$, the orientation in which $\bar G_1(\theta)$ is the steady-state mean of $Z(\phi_\theta-P_\theta\phi_\theta)'$ of p. 1156 and $\bar r(\theta)$ is the limit of the critic; the other orientation is its transpose. Vectors indexed by $\{0\}\cup\{1,\dots,m\}$ use the index type `Fin 1 ⊕ Fin m`.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), pp. 1156–1160 (R_k, §5.1 T_θ, Q_θ, h̄, Ḡ; §5.2 h̄₁, Ḡ₁, Z̄), p. 1162 (§6: H_θ, H̄, r̄, f, e⁽¹⁾, e⁽²⁾)

import Mathlib
import Definitions.Def_ActorCritic_Finite_Algorithm

namespace ActorCritic.Finite

variable {X U : Type} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U] {n m : ℕ}

/-- A function `X × U → ℝ^m` viewed as `m` real coordinate functions; used to write the
matrix-valued inner products `⟨φ_θ, φ_θ'⟩_θ` of the paper (p. 1146). -/
abbrev Feat (X U : Type) (n m : ℕ) :=
  EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m)

/-! ### TD(1): regeneration at `x*` (§5.1, p. 1157) -/

/-- The taboo matrix of the state–action chain: `P̃_θ((x, u), (y, ū)) = p(y | x, u) μ_θ(ū | y)`
if `y ≠ x*` and `0` if `y = x*`. With `τ = min{k > 0 | X_k = x*}`,
`P_{θ,x}(τ > k | U_0 = u) = (P̃_θ^k 1)(x, u)`. -/
noncomputable def tabooMatrix (M : FiniteMDP X U) (π : RSPFamily X U n) (xstar : X)
    (θ : EuclideanSpace ℝ (Fin n)) : Matrix (X × U) (X × U) ℝ :=
  fun w w' => if w'.1 = xstar then 0 else pairMatrix M π θ w w'

/-- `T_θ(x, u) = E_{θ,x}[τ | U_0 = u]` with `τ = min{k > 0 | X_k = x*}` (p. 1157), written as
`T_θ = ∑_{k ≥ 0} P̃_θ^k 1`. The series converges under Assumption 2.1(d) (if it did not,
Lean's `tsum` would return `0`; that does not happen under the assumptions of the
statements that use it). -/
noncomputable def returnTime (M : FiniteMDP X U) (π : RSPFamily X U n) (xstar : X)
    (θ : EuclideanSpace ℝ (Fin n)) : X × U → ℝ :=
  ∑' k : ℕ, (tabooMatrix M π xstar θ ^ k).mulVec (fun _ => 1)

/-- The regenerative Q-function of §5.1 (p. 1157),
`Q_θ(x, u) = E_{θ,x}[∑_{k=0}^{τ−1} (c(X_k, U_k) − ᾱ(θ)) | U_0 = u]`, written as
`∑_{k ≥ 0} P̃_θ^k (c − ᾱ(θ) 1)`. The series converges under Assumption 2.1(d) (else `tsum`
would be `0`). It is one particular solution of the Poisson equation (4.4). -/
noncomputable def Qreg (M : FiniteMDP X U) (π : RSPFamily X U n) (xstar : X)
    (θ : EuclideanSpace ℝ (Fin n)) : X × U → ℝ :=
  ∑' k : ℕ, (tabooMatrix M π xstar θ ^ k).mulVec (fun w => M.c w.1 w.2 - avgCost M π θ)

/-! ### Steady-state quantities of the critic (§5.1, p. 1158; §5.2, pp. 1159–1160) -/

/-- `⟨φ_θ, φ_θ'⟩_θ = ∑_{x,u} η_θ(x, u) φ_θ(x, u) φ_θ(x, u)'`, an `m × m` matrix. -/
noncomputable def gramPhi (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (θ : EuclideanSpace ℝ (Fin n)) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ x, ∑ u, eta M π θ x u • Matrix.vecMulVec (fun i => φ θ x u i) (fun j => φ θ x u j)

/-- The vector `h̄₁(θ) ∈ ℝ^m` of the critic:
* TD(1) (p. 1158): `h̄₁(θ) = ⟨Q_θ, φ_θ⟩_θ` with the regenerative `Q_θ` (`Qreg`);
* TD(λ) (p. 1159): `h̄₁(θ) = ∑_{k ≥ 0} λ^k ⟨P_θ^k c − ᾱ(θ) 1, φ_θ⟩_θ`. -/
noncomputable def hbar1 (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m) :
    Critic X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)
  | Critic.td1 xstar, θ => ∑ x, ∑ u, (eta M π θ x u * Qreg M π xstar θ (x, u)) • φ θ x u
  | Critic.tdLambda lam, θ => ∑' k : ℕ, lam ^ k •
      ∑ x, ∑ u, (eta M π θ x u *
        ((pairMatrix M π θ ^ k).mulVec (fun w => M.c w.1 w.2) (x, u) - avgCost M π θ)) •
          φ θ x u

/-- The vector `Z̄(θ) ∈ ℝ^m` (steady-state mean of the trace):
* TD(1) (p. 1158): `Z̄(θ) = ⟨T_θ, φ_θ⟩_θ`;
* TD(λ) (p. 1160): `Z̄(θ) = (1 − λ)^{-1} ⟨1, φ_θ⟩_θ`. -/
noncomputable def Zbar (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m) :
    Critic X → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)
  | Critic.td1 xstar, θ => ∑ x, ∑ u, (eta M π θ x u * returnTime M π xstar θ (x, u)) • φ θ x u
  | Critic.tdLambda lam, θ => (1 - lam)⁻¹ • ∑ x, ∑ u, eta M π θ x u • φ θ x u

/-- The `m × m` matrix `Ḡ₁(θ)`:
* TD(1) (p. 1158): `Ḡ₁(θ) = ⟨φ_θ, φ_θ'⟩_θ`;
* TD(λ) (p. 1159): `Ḡ₁(θ) = ⟨φ_θ, φ_θ'⟩_θ − (1 − λ) ∑_{k ≥ 0} λ^k ⟨P_θ^{k+1} φ_θ, φ_θ'⟩_θ`,
  where the `(i, j)` entry of the `k`-th term is `∑_{x,u} η_θ(x, u) φ_θ^i(x, u) (P_θ^{k+1} φ_θ^j)(x, u)`,
  the orientation that makes `Ḡ₁(θ)` the steady-state mean of `Z (φ_θ − P_θ φ_θ)'` (p. 1156). -/
noncomputable def Gbar1 (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m) :
    Critic X → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ
  | Critic.td1 _, θ => gramPhi M π φ θ
  | Critic.tdLambda lam, θ => gramPhi M π φ θ - (1 - lam) • ∑' k : ℕ, lam ^ k •
      Matrix.of (fun i j => ∑ x, ∑ u, eta M π θ x u * φ θ x u i *
        (pairMatrix M π θ ^ (k + 1)).mulVec (fun w => φ θ w.1 w.2 j) (x, u))

/-- The block vector `h̄(θ) = (L ᾱ(θ), h̄₁(θ) + ᾱ(θ) Z̄(θ)) ∈ ℝ^{1+m}` (pp. 1157, 1159), indexed by
`Fin 1 ⊕ Fin m`. -/
noncomputable def hbar (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (crit : Critic X) (L : ℝ) (θ : EuclideanSpace ℝ (Fin n)) : Fin 1 ⊕ Fin m → ℝ :=
  Sum.elim (fun _ => L * avgCost M π θ)
    (fun i => hbar1 M π φ crit θ i + avgCost M π θ * Zbar M π φ crit θ i)

/-- The block matrix `Ḡ(θ) = [[1, 0], [Z̄(θ)/L, Ḡ₁(θ)]]` (pp. 1157, 1159), indexed by
`Fin 1 ⊕ Fin m`. -/
noncomputable def Gbar (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (crit : Critic X) (L : ℝ) (θ : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℝ :=
  Matrix.fromBlocks 1 0 (fun i _ => Zbar M π φ crit θ i / L) (Gbar1 M π φ crit θ)

/-- The critic vector `R_k = (L α_k, r_k) ∈ ℝ^{1+m}` (p. 1156). -/
noncomputable def Rvec (L : ℝ) (s : ACState n m) : Fin 1 ⊕ Fin m → ℝ :=
  Sum.elim (fun _ => L * s.α) (fun i => s.r i)

/-! ### Objects of the actor analysis (§6, p. 1162) -/

/-- `H_θ(x, u) = ψ_θ(x, u) φ_θ'(x, u)`, an `n × m` matrix. -/
noncomputable def Hmat (π : RSPFamily X U n) (φ : Feat X U n m)
    (θ : EuclideanSpace ℝ (Fin n)) (w : X × U) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.vecMulVec (fun i => score π θ w.1 w.2 i) (fun j => φ θ w.1 w.2 j)

/-- `H̄(θ) = ⟨ψ_θ, φ_θ'⟩_θ = ∑_{x,u} η_θ(x, u) ψ_θ(x, u) φ_θ(x, u)'`, an `n × m` matrix. -/
noncomputable def Hbar (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (θ : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin m) ℝ :=
  ∑ x, ∑ u, eta M π θ x u • Hmat π φ θ (x, u)

/-- `r̄(θ)`, the solution of `h̄₁(θ) = Ḡ₁(θ) r̄(θ)` (p. 1162), as `Ḡ₁(θ)⁻¹ h̄₁(θ)`. Under
Assumptions 2.1 and 3.2, `Ḡ₁(θ)` is positive definite (Lemmas 5.3 and 5.6), hence invertible,
so Lean's convention `A⁻¹ = 0` for singular `A` does not intervene. -/
noncomputable def rbar (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (crit : Critic X) (θ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 ((Gbar1 M π φ crit θ)⁻¹.mulVec (fun i => hbar1 M π φ crit θ i))

/-- `f(θ) = H̄(θ) r̄(θ) ∈ ℝⁿ` (p. 1162). -/
noncomputable def fvec (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (crit : Critic X) (θ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 ((Hbar M π φ θ).mulVec (fun j => rbar M π φ crit θ j))

/-- `e^{(1)}_k = (H_{θ_k}(X̂_{k+1}, Û_{k+1}) − H̄(θ_k)) r_k Γ(r_k)` along a path `ω` (p. 1162),
with `(θ_k, r_k)` the iterates of the recursion. -/
noncomputable def noise1 (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ) (crit : Critic X) (s₀ : ACState n m)
    (ω : ℕ → X × U) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  let s := acIter M π φ β γ Γ crit s₀ ω k
  WithLp.toLp 2 ((Hmat π φ s.θ (ω (k + 1)) - Hbar M π φ s.θ).mulVec
    (fun j => Γ s.r * s.r j))

/-- `e^{(2)}_k = H̄(θ_k)(r_k Γ(r_k) − r̄(θ_k) Γ(r̄(θ_k)))` along a path `ω` (p. 1162). -/
noncomputable def noise2 (M : FiniteMDP X U) (π : RSPFamily X U n) (φ : Feat X U n m)
    (β γ : ℕ → ℝ) (Γ : EuclideanSpace ℝ (Fin m) → ℝ) (crit : Critic X) (s₀ : ACState n m)
    (ω : ℕ → X × U) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  let s := acIter M π φ β γ Γ crit s₀ ω k
  let rb := rbar M π φ crit s.θ
  WithLp.toLp 2 ((Hbar M π φ s.θ).mulVec (fun j => Γ s.r * s.r j - Γ rb * rb j))

end ActorCritic.Finite


