-- Prove2me | Definitions.Def_ActorCritic_Finite_Model
-- name    : ActorCritic_Finite_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:40.110159+00:00
-- url     : https://prove2.me/theorems/b7fd75f5-a380-4a36-b421-4826cf90c8a4
-- title:
--   §§2–4 — π_θ, η_θ, average cost ᾱ(θ), score ψ_θ, centred features φ̂_θ, Poisson equation (4.4), Assumptions 2.1, 3.1–3.3, 4.9
-- statement:
--   Fix a finite cost MDP $(\mathbb X,\mathbb U,p,c)$ and a family of RSPs $\mu_\theta$, $\theta\in\mathbb R^n$. This module defines the quantities of §§2–4 of Konda and Tsitsiklis and their standing assumptions in the finite case.
--
--   1. **Stationary laws.** $\pi_\theta$ is a stationary probability vector of $P(\theta)$, and $\eta_\theta(x,u)=\pi_\theta(x)\mu_\theta(u\mid x)$. Under Assumption 2.1(c) the stationary vector is unique.
--   2. **Average cost** $\bar\alpha(\theta)=\sum_{x,u}c(x,u)\,\eta_\theta(x,u)$.
--   3. **Score** $\psi_\theta(x,u)=\nabla\ln\mu_\theta(u\mid x)\in\mathbb R^n$.
--   4. **Centred critic features** $\hat\phi_\theta(x,u)=\phi_\theta(x,u)-\sum_{\bar x,\bar u}\eta_\theta(\bar x,\bar u)\phi_\theta(\bar x,\bar u)$ for features $\phi_\theta(x,u)\in\mathbb R^m$.
--   5. **Poisson equation (4.4).** $Q:\mathbb X\times\mathbb U\to\mathbb R$ solves it with parameter $\theta$ if
--   $$
--   Q=c-\bar\alpha(\theta)\underline 1+P_\theta Q .
--   $$
--   6. **Assumption 2.1** (finite case): (a) $\mu_\theta(u\mid x)>0$; (b) $\theta\mapsto\mu_\theta(u\mid x)$ is twice differentiable and $\theta\mapsto\psi_\theta(x,u)$ is bounded, differentiable, with bounded derivative; (c) for every $\theta$ both $P(\theta)$ and $P_\theta$ are irreducible and aperiodic; (d) there are $N\ge1$, $x^*\in\mathbb X$, $\epsilon_0>0$ with $\sum_{k=1}^N[P(\theta_1)\cdots P(\theta_k)]_{xx^*}\ge\epsilon_0$ for all $\theta_1,\dots,\theta_N$ and all $x$.
--   7. **Assumption 3.1** (critic features): (a) $\theta\mapsto\phi_\theta(x,u)$ is bounded and differentiable with bounded derivative; (b) the span $\Phi_\theta$ of the feature functions $\phi^j_\theta$ in $\mathbb R^{|\mathbb X||\mathbb U|}$ contains the span $\Psi_\theta$ of the score components $\psi^i_\theta$.
--   8. **Assumption 3.2.** There is $a>0$ with $\|r'\hat\phi_\theta\|_\theta^2=\sum_{x,u}\eta_\theta(x,u)\,(r'\hat\phi_\theta(x,u))^2\ge a|r|^2$ for all $r\in\mathbb R^m$, $\theta\in\mathbb R^n$.
--   9. **Assumption 3.3.** (a) The step sizes $\beta_k,\gamma_k$ are positive and nonincreasing, $\sum_k\beta_k=\sum_k\gamma_k=\infty$, $\sum_k\beta_k^2<\infty$, $\sum_k\gamma_k^2<\infty$ and $\sum_k(\beta_k/\gamma_k)^d<\infty$ for some $d>0$. (b) There are constants $0<C_1<C_2$ with $(1+|r|)\Gamma(r)\in[C_1,C_2]$ for all $r\in\mathbb R^m$ and $|\Gamma(r)-\Gamma(\hat r)|\le C_2|r-\hat r|/(1+|r|+|\hat r|)$ for all $r,\hat r\in\mathbb R^m$.
--   10. **Assumption 4.9** (finite case, at the state $x^*$ of 2.1(d)): $\sum_u\mu_\theta(u\mid x^*)\,\phi_\theta(x^*,u)=0$ for every $\theta$.
--
--   These are the hypotheses of Theorem 3.4, the paper's main result, and of the lemmas of §§4–6.
--
--   **Formalization Note** $\pi_\theta$ is chosen by `Classical.epsilon` among the stationary probability vectors of $P(\theta)$; one exists for every $\theta$, and under 2.1(c) it is unique, so it is the paper's $\pi_\theta$. In 3.3(b) the paper prints $|r|\Gamma(r)\in[C_1,C_2]$, which is unsatisfiable at $r=0$ (it would make Theorem 3.4 vacuous), and quantifies (3.3) over $r,\hat r\in\mathbb R^n$; this is formalized with $(1+|r|)\Gamma(r)$ and over $\mathbb R^m$, the domain of $\Gamma$, because the proofs use only that $r\Gamma(r)$ is bounded and Lipschitz and that $\Gamma$ is bounded away from $0$ on bounded sets, which this reading gives and $\Gamma(r)=1/(1+|r|)$ satisfies. In 3.3(a), positivity of $\beta_k$ is stated; it follows from the other conditions. In 2.1(b) "twice differentiable" is: differentiable with differentiable Fréchet derivative.
-- source:
--   Konda and Tsitsiklis, On Actor-Critic Algorithms, SIAM J. Control Optim. 42 (2003), pp. 1144–1149 (Assumption 2.1, ᾱ, (2.1), inner product p. 1146, Assumptions 3.1–3.3), p. 1152 ((4.4)), p. 1155 (Assumption 4.9)

import Mathlib
import Definitions.Def_ActorCritic_Finite_MDP

namespace ActorCritic.Finite

variable {X U : Type} [Fintype X] [Fintype U] {n m : ℕ}

/-- The stationary probabilities `π_θ(x)` of the state chain under the RSP `θ`
(Assumption 2.1(c), p. 1145): a probability vector `q` with `q P(θ) = q`, chosen by
`Classical.epsilon`. Under Assumption 2.1(c) the chain is irreducible, so this stationary law
exists and is unique; it is then *the* `π_θ` of the paper. -/
noncomputable def stationaryDist (M : FiniteMDP X U) (π : RSPFamily X U n)
    (θ : EuclideanSpace ℝ (Fin n)) : X → ℝ :=
  Classical.epsilon (IsStationary (stateMatrix M π θ))

/-- The stationary probabilities of the state–action chain,
`η_θ(x, u) = π_θ(x) μ_θ(u | x)` (Assumption 2.1(c), p. 1145). -/
noncomputable def eta (M : FiniteMDP X U) (π : RSPFamily X U n)
    (θ : EuclideanSpace ℝ (Fin n)) (x : X) (u : U) : ℝ :=
  stationaryDist M π θ x * π.μ θ x u

/-- The average cost `ᾱ(θ) = ∑_{x,u} c(x, u) η_θ(x, u)` (p. 1145). -/
noncomputable def avgCost (M : FiniteMDP X U) (π : RSPFamily X U n)
    (θ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ x, ∑ u, M.c x u * eta M π θ x u

/-- The score `ψ_θ(x, u) = ∇ ln μ_θ(u | x) ∈ ℝⁿ` ((2.1), p. 1145), with `∇` the gradient in `θ`
for the Euclidean inner product on `ℝⁿ`. -/
noncomputable def score (π : RSPFamily X U n) (θ : EuclideanSpace ℝ (Fin n)) (x : X) (u : U) :
    EuclideanSpace ℝ (Fin n) :=
  gradient (fun θ' => Real.log (π.μ θ' x u)) θ

/-- The centred critic features (Assumption 3.2, p. 1147):
`φ̂_θ(x, u) = φ_θ(x, u) − ∑_{x̄,ū} η_θ(x̄, ū) φ_θ(x̄, ū)`. -/
noncomputable def phiHat (M : FiniteMDP X U) (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m))
    (θ : EuclideanSpace ℝ (Fin n)) (x : X) (u : U) : EuclideanSpace ℝ (Fin m) :=
  φ θ x u - ∑ x', ∑ u', eta M π θ x' u' • φ θ x' u'

/-- `Q : X × U → ℝ` solves the Poisson equation with parameter `θ` ((4.4), p. 1152, finite case):
`Q = c − ᾱ(θ) 1 + P_θ Q`. -/
def IsPoissonSol (M : FiniteMDP X U) (π : RSPFamily X U n) (θ : EuclideanSpace ℝ (Fin n))
    (Q : X × U → ℝ) : Prop :=
  ∀ w : X × U, Q w = M.c w.1 w.2 - avgCost M π θ + (pairMatrix M π θ).mulVec Q w

/-! ### The assumptions of the paper, finite case -/

/-- Assumption 2.1(a) (p. 1144): `μ_θ(u | x) > 0` for all `x, u, θ`. -/
def Assumption21a (π : RSPFamily X U n) : Prop :=
  ∀ θ x u, 0 < π.μ θ x u

/-- Assumption 2.1(b) (p. 1144): for every `(x, u)`, `θ ↦ μ_θ(u | x)` is twice differentiable
(differentiable with differentiable derivative), and `θ ↦ ψ_θ(x, u) = ∇ ln μ_θ(u | x)` is
bounded, differentiable, and has a bounded first derivative. -/
def Assumption21b (π : RSPFamily X U n) : Prop :=
  ∀ x u,
    Differentiable ℝ (fun θ => π.μ θ x u) ∧
    Differentiable ℝ (fderiv ℝ (fun θ => π.μ θ x u)) ∧
    Differentiable ℝ (fun θ => score π θ x u) ∧
    ∃ B : ℝ, ∀ θ, ‖score π θ x u‖ ≤ B ∧ ‖fderiv ℝ (fun θ' => score π θ' x u) θ‖ ≤ B

/-- Assumption 2.1(c) (p. 1145): for every `θ`, the state chain `{X_k}` (matrix `P(θ)`) and the
state–action chain `{X_k, U_k}` (matrix `P_θ`) are irreducible and aperiodic. -/
def Assumption21c [DecidableEq X] [DecidableEq U] (M : FiniteMDP X U) (π : RSPFamily X U n) :
    Prop :=
  ∀ θ, IsIrreducible (stateMatrix M π θ) ∧ IsAperiodic (stateMatrix M π θ) ∧
    IsIrreducible (pairMatrix M π θ) ∧ IsAperiodic (pairMatrix M π θ)

/-- Assumption 2.1(d) (p. 1145), with its data `N`, `x*`, `ε₀` explicit: `N ≥ 1`, `ε₀ > 0`, and
for all `θ_1, …, θ_N` (the entries `θs 1, …, θs N` of a sequence) and all `x`,
`∑_{k=1}^{N} [P(θ_1) ⋯ P(θ_k)]_{x x*} ≥ ε₀`. -/
def Assumption21d [DecidableEq X] (M : FiniteMDP X U) (π : RSPFamily X U n) (N : ℕ) (xstar : X)
    (ε₀ : ℝ) : Prop :=
  0 < N ∧ 0 < ε₀ ∧
    ∀ θs : ℕ → EuclideanSpace ℝ (Fin n), ∀ x : X,
      ε₀ ≤ ∑ k ∈ Finset.Icc 1 N,
        (List.ofFn (fun i : Fin k => stateMatrix M π (θs (i.val + 1)))).prod x xstar

/-- Assumption 3.1 (critic features, p. 1147).
(a) For every `(x, u)`, `θ ↦ φ_θ(x, u)` is bounded and differentiable, with a bounded derivative.
(b) For every `θ`, the span `Φ_θ` of the feature functions `φ_θ^j` (`j = 1, …, m`) in
`ℝ^{|X||U|}` contains `Ψ_θ`, the span of the score components `ψ_θ^i` (`i = 1, …, n`). -/
def Assumption31 (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m)) : Prop :=
  (∀ x u,
    (∃ B : ℝ, ∀ θ, ‖φ θ x u‖ ≤ B) ∧
    Differentiable ℝ (fun θ => φ θ x u) ∧
    ∃ B : ℝ, ∀ θ, ‖fderiv ℝ (fun θ' => φ θ' x u) θ‖ ≤ B) ∧
  (∀ θ (i : Fin n),
    (fun w : X × U => score π θ w.1 w.2 i) ∈
      Submodule.span ℝ (Set.range fun j : Fin m => fun w : X × U => φ θ w.1 w.2 j))

/-- Assumption 3.2 (p. 1147): there is `a > 0` with `‖r' φ̂_θ‖²_θ ≥ a |r|²` for all `r ∈ ℝ^m`
and `θ ∈ ℝⁿ`, where `‖Q‖²_θ = ∑_{x,u} η_θ(x, u) Q(x, u)²`. -/
def Assumption32 (M : FiniteMDP X U) (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ (r : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin n)),
    a * ‖r‖ ^ 2 ≤ ∑ x, ∑ u, eta M π θ x u * (inner ℝ r (phiHat M π φ θ x u)) ^ 2

/-- Assumption 3.3(a) (pp. 1148–1149): the step sizes `β_k`, `γ_k` are deterministic, positive
and nonincreasing, `∑ β_k = ∑ γ_k = ∞`, `∑ β_k² < ∞`, `∑ γ_k² < ∞`, and
`∑ (β_k / γ_k)^d < ∞` for some `d > 0`. (Positivity of `β_k` is implied by the other conditions;
positivity of `γ_k` is stated on p. 1148.) -/
def Assumption33a (β γ : ℕ → ℝ) : Prop :=
  (∀ k, 0 < β k) ∧ (∀ k, 0 < γ k) ∧
  (∀ k, β (k + 1) ≤ β k) ∧ (∀ k, γ (k + 1) ≤ γ k) ∧
  Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, β k) Filter.atTop Filter.atTop ∧
  Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, γ k) Filter.atTop Filter.atTop ∧
  Summable (fun k => β k ^ 2) ∧ Summable (fun k => γ k ^ 2) ∧
  ∃ d : ℝ, 0 < d ∧ Summable (fun k => (β k / γ k) ^ d)

/-- Assumption 3.3(b) (p. 1149), **corrected reading**. There are constants `0 < C₁ < C₂` with
`(1 + |r|) Γ(r) ∈ [C₁, C₂]` for all `r ∈ ℝ^m`, and
`|Γ(r) − Γ(r̂)| ≤ C₂ |r − r̂| / (1 + |r| + |r̂|)` for all `r, r̂ ∈ ℝ^m` (3.3).
The paper prints `|r| Γ(r) ∈ [C₁, C₂]`, which is unsatisfiable at `r = 0`, and quantifies the
second inequality over `ℝⁿ`, a typo since `Γ` is defined on the critic space `ℝ^m`. -/
def Assumption33b {m : ℕ} (Γ : EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ < C₂ ∧
    (∀ r, C₁ ≤ (1 + ‖r‖) * Γ r ∧ (1 + ‖r‖) * Γ r ≤ C₂) ∧
    ∀ r r', |Γ r - Γ r'| ≤ C₂ * ‖r - r'‖ / (1 + ‖r‖ + ‖r'‖)

/-- Assumption 4.9 (p. 1155), finite case, at the state `x*` of Assumption 2.1(d):
`E_{θ,x*}[φ_θ(x*, U_0)] = ∑_u μ_θ(u | x*) φ_θ(x*, u) = 0` for all `θ`. (In the finite case the
set `X_0` of the paper is `{x*}`.) -/
def Assumption49 (π : RSPFamily X U n)
    (φ : EuclideanSpace ℝ (Fin n) → X → U → EuclideanSpace ℝ (Fin m)) (xstar : X) : Prop :=
  ∀ θ, ∑ u, π.μ θ xstar u • φ θ xstar u = 0

end ActorCritic.Finite


