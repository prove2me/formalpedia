-- Prove2me | Definitions.Def_SmallGainISS_Lyapunov_Network
-- name    : SmallGainISS_Lyapunov_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:40.367516+00:00
-- url     : https://prove2.me/theorems/e86fa34f-000e-4c10-b829-c9b7798adf91
-- title:
--   Interconnected system, Assumption 2.1, ISS Lyapunov functions (Definitions 2.2, 2.5), $V=\max_i\sigma_i^{-1}(V_i(x_i))$ and the Clarke gradient (2.5)
-- statement:
--   **The network** ((2.1), (2.2), p. 5). There are $n$ subsystems; subsystem $i$ has state $x_i\in\mathbb R^{N_i}$, the network state is $x=(x_1^T,\dots,x_n^T)^T\in\mathbb R^N$, $N=\sum_i N_i$, with the Euclidean norm $\|x\|^2=\sum_i\|x_i\|^2$, and the input is $u\in\mathbb R^M$. The dynamics are
--   $$\Sigma_i:\ \dot x_i=f_i(x_1,\dots,x_n,u),\qquad \Sigma:\ \dot x=f(x,u),\quad f=(f_1,\dots,f_n).$$
--
--   **Lyapunov function candidates** (Assumption 2.1, p. 6). $V:\mathbb R^d\to\mathbb R_+$ is continuous, proper and positive definite — there are $\psi_1,\psi_2\in\mathcal K_\infty$ with $\psi_1(\|x\|)\le V(x)\le\psi_2(\|x\|)$ for all $x$ — and locally Lipschitz on $\mathbb R^d\setminus\{0\}$.
--
--   **ISS Lyapunov function of the network** (Definition 2.2, p. 6). A candidate $V$ is an ISS Lyapunov function for $\dot x=f(x,u)$ if there are $\gamma\in\mathcal K$ and a positive definite $\alpha$ such that at every point $x$ of differentiability of $V$ and for every $u$,
--   $$V(x)\ge\gamma(\|u\|)\ \Longrightarrow\ \nabla V(x)f(x,u)\le-\alpha(\|x\|).\tag{2.4}$$
--
--   **ISS Lyapunov function of a subsystem** (Definition 2.5, p. 8). Given candidates $V_1,\dots,V_n$, $V_i$ is an ISS Lyapunov function for $\Sigma_i$ with gains $\gamma_{ij}\in\mathcal K_\infty\cup\{0\}$ ($j\neq i$), $\gamma_{iu}\in\mathcal K\cup\{0\}$ and $\mu_i\in\mathrm{MAF}_{n+1}$ if there is a positive definite $\alpha_i$ such that for all $x$, $u$ with $V_i$ differentiable at $x_i$,
--   $$V_i(x_i)\ge\mu_i\big(\gamma_{i1}(V_1(x_1)),\dots,\gamma_{in}(V_n(x_n)),\gamma_{iu}(\|u\|)\big)\ \Longrightarrow\ \nabla V_i(x_i)f_i(x,u)\le-\alpha_i(\|x_i\|).\tag{2.7}$$
--
--   **The rescaled maximum** (5.4), p. 14: for $\sigma_i^{-1}$ the inverses of the components of a path, $V(x)=\max_{i}\sigma_i^{-1}(V_i(x_i))$; the **active set** of (5.6) is $I(x)=\{i: V(x)=\sigma_i^{-1}(V_i(x_i))\}$.
--
--   **Clarke's generalized gradient** (2.5), p. 7: $\partial g(x)=\mathrm{conv}\{\zeta:\exists x_k\to x,\ \nabla g(x_k)\text{ exists},\ \nabla g(x_k)\to\zeta\}$.
--
--   These are the objects of Theorem 5.3 and of the steps of its proof.
--
--   **Formalization Note** Block spaces are `EuclideanSpace ℝ (Fin (N i))`, the network space is the $L^2$ product `PiLp 2` (Euclidean norm, not the sup norm), the input space is `EuclideanSpace ℝ (Fin M)`. Lyapunov functions are real-valued with an explicit nonnegativity clause, and are fed to the gains through `toNNReal`, which is the identity on their (nonnegative) values. $\nabla V(x)f(x,u)$ is the Fréchet derivative of $V$ at $x$ applied to $f(x,u)$, always guarded by differentiability. Definitions 2.2 and 2.5 are stated with their gains and rates named; the existential forms are `IsISSLyapunov` and `IsISSLyapunovSub`. The Clarke gradient is restated (`clarkeGrad`) on a general real Hilbert space with the same body as the published `ClarkeGradients.Shared.generalizedGradient`, which it equals on `EuclideanSpace ℝ (Fin d)`; it is used for $\partial V$ on $\mathbb R^N$ and $\partial\sigma_i^{-1}$ on $\mathbb R$, while $\partial V_i$ on the blocks uses the published definition. The maximum needs $n\ge 1$ (`[NeZero n]`). The existence and uniqueness of solutions assumed on p. 5 plays no role in these statements and is not formalized.
-- source:
--   Dashkovskiy, Rüffer, Wirth, Small Gain Theorems for Large Scale Systems and Construction of ISS Lyapunov Functions, arXiv:0901.1842v2, pp. 5-8, 14, (2.1), (2.2), Assumption 2.1, Definition 2.2, (2.5), Definition 2.5, (5.4), (5.6)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_SmallGainISS_Lyapunov_Gains

open scoped NNReal
open Filter Topology

namespace SmallGainISS.Lyapunov

/-! Dashkovskiy, Rüffer, Wirth, arXiv:0901.1842v2: the interconnected system (2.1), (2.2)
(p. 5), Lyapunov function candidates (Assumption 2.1, p. 6), ISS Lyapunov functions for the
network (Definition 2.2, p. 6) and for the subsystems (Definition 2.5, p. 8), the Clarke
generalized gradient (2.5) (p. 7) and the rescaled maximum (5.4) (p. 14).

Block `i` has state space `ℝ^{Nᵢ}` = `EuclideanSpace ℝ (Fin (N i))`; the network state is
`x = (x₁ᵀ, …, xₙᵀ)ᵀ ∈ ℝᴺ`, the `L²` product `PiLp 2`, whose norm is the Euclidean norm
`‖x‖² = Σᵢ ‖xᵢ‖²`; the input is `u ∈ ℝᴹ` = `EuclideanSpace ℝ (Fin M)`. -/

variable {n : ℕ} {N : Fin n → ℕ} {M : ℕ}

/-- The state space `ℝ^{Nᵢ}` of subsystem `i`. -/
abbrev Block (N : Fin n → ℕ) (i : Fin n) := EuclideanSpace ℝ (Fin (N i))

/-- The network state space `ℝᴺ`, `N = Σ Nᵢ`, with the Euclidean norm. -/
abbrev State (N : Fin n → ℕ) := PiLp 2 (fun i : Fin n => Block N i)

/-- The input space `ℝᴹ`. -/
abbrev Input (M : ℕ) := EuclideanSpace ℝ (Fin M)

/-- The overall right-hand side `f = (f₁, …, fₙ)` of `Σ : ẋ = f(x, u)` (2.2), assembled from the
subsystem right-hand sides `fᵢ : ℝ^{N+M} → ℝ^{Nᵢ}` of (2.1). -/
noncomputable def netF (f : (i : Fin n) → State N → Input M → Block N i)
    (x : State N) (u : Input M) : State N :=
  WithLp.toLp 2 (fun i => f i x u)

/-- Assumption 2.1 (p. 6), with "proper and positive definite" from p. 5: `V : ℝᵈ → ℝ₊` is
continuous; there are `ψ₁, ψ₂ ∈ 𝒦∞` with `ψ₁(‖x‖) ≤ V(x) ≤ ψ₂(‖x‖)` for all `x`; and `V` is
locally Lipschitz continuous on `ℝᵈ \ {0}`. `V` is real-valued (so that it can be
differentiated) and nonnegative. -/
def IsLyapCandidate {E : Type*} [NormedAddCommGroup E] (V : E → ℝ) : Prop :=
  Continuous V ∧ (∀ x, 0 ≤ V x) ∧
  (∃ ψ₁ ψ₂ : ℝ≥0 → ℝ≥0, IsKInf ψ₁ ∧ IsKInf ψ₂ ∧
    ∀ x, (ψ₁ ‖x‖₊ : ℝ) ≤ V x ∧ V x ≤ (ψ₂ ‖x‖₊ : ℝ)) ∧
  LocallyLipschitzOn ({0}ᶜ : Set E) V

/-- Definition 2.2 (p. 6) with the gain `γ` and the rate `α` named: `V` satisfies
Assumption 2.1, `γ ∈ 𝒦`, `α` is positive definite, and at all points of differentiability of
`V`, `V(x) ≥ γ(‖u‖) ⟹ ∇V(x) f(x, u) ≤ −α(‖x‖)` (2.4), for every input value `u`. -/
def IsISSLyapunovWith {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] (V : E → ℝ) (F : E → U → E) (γ α : ℝ≥0 → ℝ≥0) : Prop :=
  IsLyapCandidate V ∧ IsK γ ∧ IsPosDef α ∧
  ∀ x u, DifferentiableAt ℝ V x → (γ ‖u‖₊ : ℝ) ≤ V x →
    fderiv ℝ V x (F x u) ≤ -(α ‖x‖₊ : ℝ)

/-- Definition 2.2 (p. 6): `V` is an ISS Lyapunov function for `ẋ = F(x, u)` if there exist
`γ ∈ 𝒦` and a positive definite `α` such that (2.4) holds. -/
def IsISSLyapunov {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] (V : E → ℝ) (F : E → U → E) : Prop :=
  ∃ γ α : ℝ≥0 → ℝ≥0, IsISSLyapunovWith V F γ α

/-- The argument `(γᵢ₁(V₁(x₁)), …, γᵢₙ(Vₙ(xₙ)), γᵢᵤ(‖u‖)) ∈ ℝⁿ⁺¹₊` of `μᵢ` in (2.7). -/
noncomputable def issArgs (Vb : (j : Fin n) → Block N j → ℝ) (Γ : GainMatrix n)
    (γu : Fin n → ℝ≥0 → ℝ≥0) (i : Fin n) (x : State N) (u : Input M) : Fin (n + 1) → ℝ≥0 :=
  appendLast (fun j => Γ i j (Vb j (x j)).toNNReal) (γu i ‖u‖₊)

/-- Definition 2.5 (p. 8) with the given ISS Lyapunov gains `γᵢⱼ` (row `i` of `Γ`), `γᵢᵤ`, the
MAF `μᵢ` and the rate `αᵢ`: every `Vⱼ` satisfies Assumption 2.1, `μᵢ ∈ MAF_{n+1}`,
`γᵢⱼ ∈ 𝒦∞ ∪ {0}` for `j ≠ i`, `γᵢᵤ ∈ 𝒦 ∪ {0}`, `αᵢ` is positive definite, and for all `x ∈ ℝᴺ`,
`u ∈ ℝᴹ` such that `Vᵢ` is differentiable at `xᵢ`,
`Vᵢ(xᵢ) ≥ μᵢ(γᵢ₁(V₁(x₁)), …, γᵢₙ(Vₙ(xₙ)), γᵢᵤ(‖u‖)) ⟹ ∇Vᵢ(xᵢ) fᵢ(x, u) ≤ −αᵢ(‖xᵢ‖)` (2.7). -/
def IsISSLyapunovSubWith (Vb : (j : Fin n) → Block N j → ℝ)
    (f : (i : Fin n) → State N → Input M → Block N i) (Γ : GainMatrix n)
    (γu : Fin n → ℝ≥0 → ℝ≥0) (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0) (i : Fin n)
    (αi : ℝ≥0 → ℝ≥0) : Prop :=
  (∀ j, IsLyapCandidate (Vb j)) ∧ IsMAF (μ i) ∧ (∀ j, j ≠ i → IsKInfOrZero (Γ i j)) ∧
  IsKOrZero (γu i) ∧ IsPosDef αi ∧
  ∀ (x : State N) (u : Input M), DifferentiableAt ℝ (Vb i) (x i) →
    μ i (issArgs Vb Γ γu i x u) ≤ (Vb i (x i)).toNNReal →
    fderiv ℝ (Vb i) (x i) (f i x u) ≤ -(αi ‖x i‖₊ : ℝ)

/-- Definition 2.5 (p. 8): `Vᵢ` is an ISS Lyapunov function for `Σᵢ` with the gains `Γ`, `γu` and
the MAF `μ` if (2.7) holds for some positive definite `αᵢ`. -/
def IsISSLyapunovSub (Vb : (j : Fin n) → Block N j → ℝ)
    (f : (i : Fin n) → State N → Input M → Block N i) (Γ : GainMatrix n)
    (γu : Fin n → ℝ≥0 → ℝ≥0) (μ : Fin n → (Fin (n + 1) → ℝ≥0) → ℝ≥0) (i : Fin n) : Prop :=
  ∃ αi : ℝ≥0 → ℝ≥0, IsISSLyapunovSubWith Vb f Γ γu μ i αi

/-- The candidate (5.4) (p. 14): `V(x) = maxᵢ σᵢ⁻¹(Vᵢ(xᵢ))`, with `τᵢ = σᵢ⁻¹`. -/
noncomputable def netV [NeZero n] (Vb : (j : Fin n) → Block N j → ℝ)
    (τ : Fin n → ℝ≥0 → ℝ≥0) (x : State N) : ℝ :=
  ((Finset.univ.sup' Finset.univ_nonempty fun i => τ i (Vb i (x i)).toNNReal : ℝ≥0) : ℝ)

/-- The active index set `I` of (5.6) (p. 14): the `i` with `V(x) = σᵢ⁻¹(Vᵢ(xᵢ))`
(equivalently `σᵢ⁻¹(Vᵢ(xᵢ)) ≥ max_{j≠i} σⱼ⁻¹(Vⱼ(xⱼ))`). -/
def activeSet [NeZero n] (Vb : (j : Fin n) → Block N j → ℝ) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (x : State N) : Set (Fin n) :=
  {i | netV Vb τ x = (τ i (Vb i (x i)).toNNReal : ℝ)}

/-- The set of limits `lim ∇g(x + hₖ)` along `hₖ → 0` with `g` differentiable at every
`x + hₖ`, on a general real Hilbert space. On `EuclideanSpace ℝ (Fin d)` it is literally the
published `ClarkeGradients.Shared.gradientLimits`. -/
def gradLimits {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (g : F → ℝ) (x : F) : Set F :=
  {ζ | ∃ h : ℕ → F, Tendsto h atTop (𝓝 0) ∧
    (∀ k, DifferentiableAt ℝ g (x + h k)) ∧
    Tendsto (fun k => gradient g (x + h k)) atTop (𝓝 ζ)}

/-- Clarke's generalized gradient (2.5) (p. 7), `∂g(x) = conv{lim ∇g(xₖ) : xₖ → x}`, on a general
real Hilbert space (used for `∂V` on `ℝᴺ` and for `∂σᵢ⁻¹` on `ℝ`). On `EuclideanSpace ℝ (Fin d)`
it is literally the published `ClarkeGradients.Shared.generalizedGradient`, which is used for
`∂Vᵢ` on the blocks. -/
def clarkeGrad {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (g : F → ℝ) (x : F) : Set F :=
  convexHull ℝ (gradLimits g x)

end SmallGainISS.Lyapunov


