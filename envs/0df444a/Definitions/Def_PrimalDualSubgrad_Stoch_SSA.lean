-- Prove2me | Definitions.Def_PrimalDualSubgrad_Stoch_SSA
-- name    : PrimalDualSubgrad_Stoch_SSA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:20.045107+00:00
-- url     : https://prove2.me/theorems/19059824-1235-4548-a3df-978465d5af3e
-- title:
--   Stochastic problem (6.1), Assumptions 1–2, and the Method of Stochastic Simple Averages (6.3)
-- statement:
--   Let $(\Xi, \mu)$ be a probability space and $Q \subseteq E$ a closed convex set with prox-function $d$, prox-center $x_0$ and argmin map $\pi_\beta$. A cost $f : Q \times \Xi \to \mathbb R$ and a stochastic oracle $f' : Q \times \Xi \to E^*$ satisfy the **standing assumptions of §6** with constant $L$ if
--
--   1. $\xi \mapsto f(x, \xi)$ is $\mu$-integrable for every $x \in Q$, so that $\varphi(x) = \mathbb E_\xi f(x, \xi)$ is well defined;
--   2. (Assumption 1) $f(\cdot, \xi)$ is convex on $Q$ for every $\xi$;
--   3. (Assumption 2) $f'(x, \xi)$ is a subgradient of $f(\cdot, \xi)$ at $x$ relative to $Q$, that is $f(x,\xi) + \langle f'(x, \xi), y - x\rangle \le f(y, \xi)$ for all $y \in Q$; and $\|f'(x, \xi)\|_* \le L$ for all $x \in Q$, $\xi \in \Xi$;
--   4. $f$ and $f'$ are jointly measurable in $(x, \xi)$.
--
--   The objective of the stochastic problem (6.1) is
--   $$\varphi(x) = \mathbb E_\xi\, f(x, \xi) = \int_\Xi f(x, \xi)\, \mu(d\xi).$$
--
--   Given $\gamma > 0$ and a sample path $\xi_0, \xi_1, \dots \in \Xi$, the **method of stochastic simple averages** sets $s_0 = 0$, $x_0$ = the prox-center, and for $k \ge 0$
--   $$g_k = f'(x_k, \xi_k), \qquad s_{k+1} = s_k + g_k, \qquad x_{k+1} = \pi_{\gamma\hat\beta_{k+1}}(-s_{k+1}).$$
--   Thus $x_{k+1}$ is a function of $(\xi_0, \dots, \xi_k)$. For $k \ge 0$ the vector $\boldsymbol\xi_k = (\xi_0, \dots, \xi_k)$ consists of $k+1$ independent copies of $\xi \sim \mu$; its law is the product measure $\mu^{\otimes(k+1)}$, and $\mathbb E_{\boldsymbol\xi_k}$ is the integral against it.
--
--   These objects state the expected-accuracy guarantee of the stochastic method and the intermediate inequalities of its proof.
--
--   **Formalization Note** $f$ and $f'$ are functions on $E \times \Xi$ whose values off $Q$ play no role, and the subgradient is relative to $Q$, as the paper gives $f$ on $Q \times \Xi$ only. Joint measurability (of $f$, and of each $(x,\xi) \mapsto \langle f'(x,\xi), y\rangle$, which in finite dimension is measurability of $f'$) is not written in the paper, which takes expectations of $f(x_i, \xi_i)$ and $\varphi(\bar x_k)$ without comment; it is added because a non-measurable integrand would have Lean integral $0$. A finite sample $(\xi_0, \dots, \xi_k)$ is extended to an infinite sequence by repeating $\xi_0$; the iterates $x_0, \dots, x_{k+1}$ and the gap $\delta_k$ never read the padding.
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), p. 25, (6.1), Assumptions 1 and 2; p. 26, (6.3) and the definition of ξ_k

import Mathlib
import Definitions.Def_PrimalDualSubgrad_Stoch_ProxSetting

namespace PrimalDualSubgrad.Stoch

open Finset MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- Nesterov 2009, p. 25: the standing assumptions of §6 on the cost `f : Q × Ξ → ℝ` (modelled
as a real function on `E × Ξ` whose values off `Q` play no role) and the stochastic oracle `f'`.
* `integrable`: the expectation `E_ξ f(x, ξ)` is well defined for every `x ∈ Q`;
* `convex`: Assumption 1, `f(·, ξ)` is convex on `Q` for every `ξ`;
* `subgrad`: Assumption 2, `f'(x, ξ)` is a subgradient of `f(·, ξ)` at `x` relative to `Q`;
* `bound`: Assumption 2, `‖f'(x, ξ)‖_* ≤ L` for all `x ∈ Q`, `ξ ∈ Ξ`;
* `meas_f`, `meas_f'`: joint measurability of `f` and of `f'` (weakly: each `⟨f'(·,·), y⟩`), which the
  paper uses tacitly when it takes expectations of `f(x_i, ξ_i)` and `φ(x̄_k)`. -/
structure StochOracle (Q : Set E) (μ : Measure Ξ) (f : E → Ξ → ℝ)
    (f' : E → Ξ → StrongDual ℝ E) (L : ℝ) : Prop where
  integrable : ∀ x ∈ Q, Integrable (fun ξ => f x ξ) μ
  convex : ∀ ξ, ConvexOn ℝ Q (fun x => f x ξ)
  subgrad : ∀ x ∈ Q, ∀ ξ, ∀ y ∈ Q, f x ξ + f' x ξ (y - x) ≤ f y ξ
  bound : ∀ x ∈ Q, ∀ ξ, ‖f' x ξ‖ ≤ L
  meas_f : Measurable (fun p : E × Ξ => f p.1 p.2)
  meas_f' : ∀ y : E, Measurable (fun p : E × Ξ => f' p.1 p.2 y)

/-- Nesterov 2009, p. 25, (6.1): the objective `φ(x) = E_ξ f(x, ξ)`. -/
noncomputable def expectedCost (μ : Measure Ξ) (f : E → Ξ → ℝ) (x : E) : ℝ :=
  ∫ ξ, f x ξ ∂μ

/-- The state `(x_k, s_k)` of the Method of Stochastic Simple Averages (Nesterov 2009, p. 26,
(6.3)) along a sample path `ω = (ξ₀, ξ₁, …)`: `x₀` is the prox-center, `s₀ = 0`,
`s_{k+1} = s_k + f'(x_k, ξ_k)`, `x_{k+1} = π_{γ β̂_{k+1}}(-s_{k+1})`. -/
noncomputable def ssaState (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E)
    (f' : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) : ℕ → E × StrongDual ℝ E
  | 0 => (x0, 0)
  | (k + 1) =>
    let s := (ssaState π γ x0 f' ω k).2 + f' (ssaState π γ x0 f' ω k).1 (ω k)
    (π (γ * betaHat (k + 1)) (-s), s)

/-- The SSA iterates `x_k = x_k(ξ₀, …, ξ_{k-1})` along the sample path `ω` (Nesterov 2009, p. 26). -/
noncomputable def ssaRun (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E)
    (f' : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) (k : ℕ) : E :=
  (ssaState π γ x0 f' ω k).1

/-- A finite sample `(ξ₀, …, ξ_k)` extended to a sequence indexed by `ℕ`; indices beyond `k` are
filled with `ξ₀`. The SSA iterates `x₀, …, x_{k+1}` and the gap `δ_k` never read them. -/
def padSample {k : ℕ} (ω : Fin (k + 1) → Ξ) : ℕ → Ξ :=
  fun i => if h : i < k + 1 then ω ⟨i, h⟩ else ω 0

/-- The law of `ξ^k = (ξ₀, …, ξ_k)`: `k + 1` independent copies of `ξ ∼ μ`. -/
noncomputable def sampleLaw (μ : Measure Ξ) (k : ℕ) : Measure (Fin (k + 1) → Ξ) :=
  Measure.pi fun _ : Fin (k + 1) => μ

end PrimalDualSubgrad.Stoch


