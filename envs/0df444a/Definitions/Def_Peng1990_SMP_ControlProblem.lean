-- Prove2me | Definitions.Def_Peng1990_SMP_ControlProblem
-- name    : Peng1990_SMP_ControlProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:30:24.986361+00:00
-- url     : https://prove2.me/theorems/ae92048a-0e80-4c1b-aec5-858bd01ba398
-- title:
--   The stochastic control problem (1)–(2), assumption (3), admissible and optimal controls, spike variation, Hamiltonian
-- statement:
--   Let $n,k,d\ge0$. The data of the problem are a horizon $T>0$, an initial state $x_0\in\mathbb R^n$, a nonempty control domain $U\subseteq\mathbb R^k$ (not assumed convex, closed or bounded), and functions
--   $$g:\mathbb R^n\times\mathbb R^k\to\mathbb R^n,\quad \sigma=(\sigma^1,\dots,\sigma^d),\ \sigma^j:\mathbb R^n\times\mathbb R^k\to\mathbb R^n,\quad l:\mathbb R^n\times\mathbb R^k\to\mathbb R,\quad h:\mathbb R^n\to\mathbb R .$$
--
--   1. **Assumption (3).** $g,\sigma,l,h$ are twice continuously differentiable in $x$; they and their derivatives $g_x,g_{xx},\sigma_x,\sigma_{xx},l_x,l_{xx},h_x,h_{xx}$ are continuous in $(x,v)$; $g_x,g_{xx},\sigma_x,\sigma_{xx},l_{xx},h_{xx}$ are bounded; and $g,\sigma,l_x,h_x$ are bounded by $C(1+|x|+|v|)$, with one constant $C$.
--   2. **Admissible control.** An $\mathcal F^t$-progressive process $v$ with values in $U$ such that $\sup_{0\le t\le T}E|v(t)|^m<\infty$ for every $m=1,2,\dots$.
--   3. **State equation (1).** $x$ is a trajectory for $v$ when
--   $$dx(t)=g(x(t),v(t))\,dt+\sum_{j=1}^d\sigma^j(x(t),v(t))\,dB^j(t),\qquad x(0)=x_0 .$$
--   4. **Cost (2).** $J(v)=E\int_0^T l(x(t),v(t))\,dt+E\,h(x(T))$. A pair $(y,u)$ is **optimal** when $u$ is admissible, $y$ is its trajectory, $J(u)$ is finite, and $J(u)\le J(v)$ for every admissible $v$ with trajectory $x$ and finite cost.
--   5. **Spike variation.** For $0\le\tau<T$, $\varepsilon>0$ and a random variable $v$,
--   $$u^\varepsilon(t)=\begin{cases}v,&\tau\le t\le\tau+\varepsilon,\\u(t),&\text{otherwise.}\end{cases}$$
--   6. **Hamiltonian.** $H(x,v,p,K)=l(x,v)+(p,g(x,v))+\sum_{j=1}^d(K_j,\sigma^j(x,v))$ for $p\in\mathbb R^n$, $K=(K_1,\dots,K_d)\in(\mathbb R^n)^d$; $H_{xx}$ is its Hessian in $x$; and $\sigma\sigma^*(x,v)=\sum_j\sigma^j(x,v)\sigma^j(x,v)^*$.
--   7. **Derivative notation.** $f_x$ is the Jacobian (gradient for scalar $f$), $f_{xx}yy=\sum_{i,j}f_{x^ix^j}y^iy^j$, and $h_{xx}$ is the Hessian matrix.
--
--   This is the model of Theorem 3; every other item of the mission is stated on it.
--
--   **Formalization Note** States, controls and noise are `Fin n → ℝ`, `Fin k → ℝ`, `Fin d → ℝ` with the sup norm (all norms on $\mathbb R^n$ are equivalent, and norms enter only through bounds with an unspecified constant). Derivatives are Fréchet derivatives (`fderiv`), bounded in operator norm. The paper does not say that $J(v)$ is finite; optimality is read among controls of finite cost, and the optimal cost itself is required finite (`CostIntegrable`). Admissible controls take values in $U$ at every time.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, pp. 967–968, Section 2, (1), (2), (3); p. 968, spike variation; p. 972, definition of $H$ (printed with the misprint $o^j$ for $\sigma^j$); p. 968, definition of $f_{xx}yy$

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The data of the stochastic control problem (1)–(2): horizon `T > 0`, initial state `x₀`,
a nonempty control domain `U ⊆ ℝᵏ`, drift `g`, diffusion columns `σ = (σ¹, …, σᵈ)`
(`σ(x, v) ∈ 𝓛(ℝᵈ, ℝⁿ)` is the matrix with columns `σʲ(x, v)`), running cost `l`, terminal
cost `h`. -/
structure ControlProblem (n k d : ℕ) where
  T : ℝ≥0
  hT : 0 < T
  x₀ : Fin n → ℝ
  U : Set (Fin k → ℝ)
  hU : U.Nonempty
  g : (Fin n → ℝ) → (Fin k → ℝ) → (Fin n → ℝ)
  σ : Fin d → (Fin n → ℝ) → (Fin k → ℝ) → (Fin n → ℝ)
  l : (Fin n → ℝ) → (Fin k → ℝ) → ℝ
  h : (Fin n → ℝ) → ℝ

/-- Gradient `f_x(x)` of a scalar function (vector of partial derivatives). -/
noncomputable def grad {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ f x (Pi.single i 1)

/-- Jacobian matrix `f_x(x)` of a vector function: entry `(i, j)` is `∂fⁱ/∂xʲ`. -/
noncomputable def jac {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ f x (Pi.single j 1) i

/-- The second derivative applied twice to `y`: `f_xx(x) y y = Σ_{i,j} f_{xⁱxʲ}(x) yⁱ yʲ`. -/
noncomputable def d2 {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (Fin n → ℝ) → F) (x y : Fin n → ℝ) : F :=
  fderiv ℝ (fderiv ℝ f) x y y

/-- Hessian matrix `f_xx(x)` of a scalar function: entry `(i, j)` is `∂²f/∂xⁱ∂xʲ`. -/
noncomputable def hess {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)

variable {n k d : ℕ}

/-- Assumption (3): `g, σ, l, h` are twice continuously differentiable in `x`; they and their
first and second `x`-derivatives are continuous in `(x, v)`; `g_x, g_xx, σ_x, σ_xx, l_xx, h_xx`
are bounded, and `g, σ, l_x, h_x` are bounded by `C(1 + |x| + |v|)`. -/
structure Assumption3 (cp : ControlProblem n k d) : Prop where
  g_c2 : ∀ v, ContDiff ℝ 2 (fun x => cp.g x v)
  σ_c2 : ∀ j v, ContDiff ℝ 2 (fun x => cp.σ j x v)
  l_c2 : ∀ v, ContDiff ℝ 2 (fun x => cp.l x v)
  h_c2 : ContDiff ℝ 2 cp.h
  g_cont : Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) => cp.g q.1 q.2)
  gx_cont : Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) => fderiv ℝ (fun x => cp.g x q.2) q.1)
  gxx_cont : Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) =>
    fderiv ℝ (fderiv ℝ (fun x => cp.g x q.2)) q.1)
  σ_cont : ∀ j, Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) => cp.σ j q.1 q.2)
  σx_cont : ∀ j, Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) =>
    fderiv ℝ (fun x => cp.σ j x q.2) q.1)
  σxx_cont : ∀ j, Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) =>
    fderiv ℝ (fderiv ℝ (fun x => cp.σ j x q.2)) q.1)
  l_cont : Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) => cp.l q.1 q.2)
  lx_cont : Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) => fderiv ℝ (fun x => cp.l x q.2) q.1)
  lxx_cont : Continuous (fun q : (Fin n → ℝ) × (Fin k → ℝ) =>
    fderiv ℝ (fderiv ℝ (fun x => cp.l x q.2)) q.1)
  h_cont : Continuous cp.h
  hx_cont : Continuous (fderiv ℝ cp.h)
  hxx_cont : Continuous (fderiv ℝ (fderiv ℝ cp.h))
  bounds : ∃ C : ℝ, ∀ (x : Fin n → ℝ) (v : Fin k → ℝ),
    ‖fderiv ℝ (fun x => cp.g x v) x‖ ≤ C ∧
    ‖fderiv ℝ (fderiv ℝ (fun x => cp.g x v)) x‖ ≤ C ∧
    (∀ j, ‖fderiv ℝ (fun x => cp.σ j x v) x‖ ≤ C) ∧
    (∀ j, ‖fderiv ℝ (fderiv ℝ (fun x => cp.σ j x v)) x‖ ≤ C) ∧
    ‖fderiv ℝ (fderiv ℝ (fun x => cp.l x v)) x‖ ≤ C ∧
    ‖fderiv ℝ (fderiv ℝ cp.h) x‖ ≤ C ∧
    ‖cp.g x v‖ ≤ C * (1 + ‖x‖ + ‖v‖) ∧
    (∀ j, ‖cp.σ j x v‖ ≤ C * (1 + ‖x‖ + ‖v‖)) ∧
    ‖fderiv ℝ (fun x => cp.l x v) x‖ ≤ C * (1 + ‖x‖ + ‖v‖) ∧
    ‖fderiv ℝ cp.h x‖ ≤ C * (1 + ‖x‖ + ‖v‖)

/-- An admissible control: a progressively measurable (for `𝓕`) `U`-valued process `v` with
`sup_{0 ≤ t ≤ T} E|v(t)|ᵐ < ∞` for every `m = 1, 2, …`. -/
def IsAdmissible (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (v : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  IsStronglyProgressive 𝓕 v ∧ (∀ t ω, v t ω ∈ cp.U) ∧
    ∀ m : ℕ, 1 ≤ m → (⨆ t ≤ cp.T, ∫⁻ ω, ‖v t ω‖ₑ ^ m ∂P) < ⊤

/-- `x` is a trajectory of the controlled system (1) for the control `v`:
`dx = g(x, v) dt + σ(x, v) dB`, `x(0) = x₀`, on `[0, T]`. -/
def SolvesState (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (v : ℝ≥0 → Ω → Fin k → ℝ) (x : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE 𝓕 P cp.T B cp.x₀ (fun s ω z => cp.g z (v s ω)) (fun j s ω z => cp.σ j z (v s ω)) x

/-- The two parts of the cost (2) are finite: `(t, ω) ↦ l(x(t), v(t))` is integrable on
`[0, T] × Ω` and `h(x(T))` is integrable. -/
def CostIntegrable (cp : ControlProblem n k d) (P : Measure Ω)
    (x : ℝ≥0 → Ω → Fin n → ℝ) (v : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  Integrable (fun q : ℝ × Ω => cp.l (x q.1.toNNReal q.2) (v q.1.toNNReal q.2))
      ((volume.restrict (Set.Icc (0 : ℝ) cp.T)).prod P) ∧
    Integrable (fun ω => cp.h (x cp.T ω)) P

/-- The cost functional (2): `J(v) = E ∫₀ᵀ l(x(t), v(t)) dt + E h(x(T))`. -/
noncomputable def cost (cp : ControlProblem n k d) (P : Measure Ω)
    (x : ℝ≥0 → Ω → Fin n → ℝ) (v : ℝ≥0 → Ω → Fin k → ℝ) : ℝ :=
  (∫ ω, ∫ t in Set.Icc (0 : ℝ) cp.T, cp.l (x t.toNNReal ω) (v t.toNNReal ω) ∂volume ∂P)
    + ∫ ω, cp.h (x cp.T ω) ∂P

/-- `(y, u)` is an optimal pair of (1)–(2): `u` is admissible, `y` is its trajectory, its cost
is finite, and its cost is at most that of every admissible control `v` with trajectory `x` and
finite cost. -/
def IsOptimalPair (cp : ControlProblem n k d) (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ) : Prop :=
  IsAdmissible cp 𝓕 P u ∧ SolvesState cp 𝓕 P B u y ∧ CostIntegrable cp P y u ∧
    ∀ (v : ℝ≥0 → Ω → Fin k → ℝ) (x : ℝ≥0 → Ω → Fin n → ℝ),
      IsAdmissible cp 𝓕 P v → SolvesState cp 𝓕 P B v x → CostIntegrable cp P x v →
        cost cp P y u ≤ cost cp P x v

/-- The spike variation of `u`: `u^ε(t) = v` if `τ ≤ t ≤ τ + ε`, `u(t)` otherwise. -/
noncomputable def spike (u : ℝ≥0 → Ω → Fin k → ℝ) (τ : ℝ≥0) (ε : ℝ) (v : Ω → Fin k → ℝ) :
    ℝ≥0 → Ω → Fin k → ℝ :=
  fun s ω => if τ ≤ s ∧ (s : ℝ) ≤ τ + ε then v ω else u s ω

/-- The Hamiltonian `H(x, v, p, K) = l(x, v) + (p, g(x, v)) + Σⱼ (Kⱼ, σʲ(x, v))`. -/
noncomputable def ham (cp : ControlProblem n k d) (x : Fin n → ℝ) (v : Fin k → ℝ)
    (p : Fin n → ℝ) (K : Fin d → Fin n → ℝ) : ℝ :=
  cp.l x v + p ⬝ᵥ cp.g x v + ∑ j, K j ⬝ᵥ cp.σ j x v

/-- `H_xx(x, v, p, K)`: the Hessian of the Hamiltonian in `x`. -/
noncomputable def hamXX (cp : ControlProblem n k d) (x : Fin n → ℝ) (v : Fin k → ℝ)
    (p : Fin n → ℝ) (K : Fin d → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  hess (fun x' => ham cp x' v p K) x

/-- `σσ*(x, v) = Σⱼ σʲ(x, v) σʲ(x, v)*`, an `n × n` matrix. -/
noncomputable def sigmaSigmaT (cp : ControlProblem n k d) (x : Fin n → ℝ) (v : Fin k → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ j, Matrix.vecMulVec (cp.σ j x v) (cp.σ j x v)

end Peng1990.SMP


