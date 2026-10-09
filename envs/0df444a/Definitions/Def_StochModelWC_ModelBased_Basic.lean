-- Prove2me | Definitions.Def_StochModelWC_ModelBased_Basic
-- name    : StochModelWC_ModelBased_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:49:42.279989+00:00
-- url     : https://prove2.me/theorems/3263e613-3773-4ed0-a1f2-a9ee110c77ab
-- title:
--   Closed extended-valued functions, weak convexity, Moreau envelope, proximal points, the iterate run
-- statement:
--   This module fixes the basic vocabulary of Davis–Drusvyatskiy, *Stochastic Model-Based Minimization of Weakly Convex Functions*, on the Euclidean space $\mathbb R^d$.
--
--   **Extended-valued functions.** A function $\psi:\mathbb R^d\to\mathbb R\cup\{+\infty\}$ is described by its domain $D=\operatorname{dom}\psi=\{x:\psi(x)<\infty\}$ together with its real values on $D$; values of the real function off $D$ play no role.
--
--   1. **Closedness** (p. 7). $\psi$ is *closed* when its epigraph is closed, i.e. when
--   $$\{(x,t)\in\mathbb R^d\times\mathbb R:\ x\in D,\ \psi(x)\le t\}$$
--   is a closed subset of $\mathbb R^d\times\mathbb R$.
--   2. **Weak convexity** (p. 8). For a real $\rho$, $\psi$ is *$\rho$-weakly convex* when $x\mapsto\psi(x)+\frac{\rho}{2}\|x\|^2$ is a convex function; in the extended-valued sense this means that $D$ is convex and the function is convex on $D$. A negative $\rho$ expresses $(-\rho)$-strong convexity.
--   3. **Moreau envelope** (2.6), p. 11. For $\lambda>0$,
--   $$\psi_\lambda(x)=\min_{y}\Big\{\psi(y)+\frac{1}{2\lambda}\|y-x\|^2\Big\},$$
--   where only $y\in D$ contribute.
--   4. **Proximal points** (2.6), p. 11. A point $p$ is a proximal point $p=\operatorname{prox}_{\lambda\psi}(x)$ when $p\in D$ minimizes $y\mapsto\psi(y)+\frac{1}{2\lambda}\|y-x\|^2$ over $D$.
--   5. **Iterate run.** Given an update rule $u_t(x,\xi)$, a starting point $x_0$ and samples $\omega=(\omega_0,\dots,\omega_{N-1})$, the run is $x_{t+1}=u_t(x_t,\omega_t)$ for $t<N$, frozen at $x_N$ afterwards.
--
--   These objects are shared by every statement of the mission: the stationarity measure of the paper is the gradient of the Moreau envelope $\varphi_{1/\bar\rho}$, and the algorithm is a run of a stochastic update.
--
--   **Formalization Note** The Moreau envelope is a real infimum over the subtype $D$; it is the junk value $0$ when $D$ is empty or the family is unbounded below. Every theorem that uses it carries hypotheses (proper, closed, weakly convex with $\lambda<\rho^{-1}$) under which the infimum is attained (Lemma 2.2). The parameter $\lambda$ is written `lam`, since `λ` is a Lean keyword.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, pp. 7–8 (domain, epigraph, closed, ρ-weakly convex), p. 11, (2.6); p. 19, Algorithm 4.1 (the iteration)

import Mathlib

open MeasureTheory Filter Topology

namespace StochModelWC.ModelBased

/-- An extended-valued function `ψ : ℝ^d → ℝ ∪ {∞}` is encoded by its domain `D = dom ψ` and its (real) values on
`D`; values off `D` are irrelevant. `ψ` is closed (p. 7: `epi ψ` closed) iff this set is closed. -/
def IsClosedFn {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  IsClosed {p : EuclideanSpace ℝ (Fin d) × ℝ | p.1 ∈ D ∧ ψ p.1 ≤ p.2}

/-- p. 8: `ψ` (with domain `D`) is `ρ`-weakly convex: `x ↦ ψ x + ρ/2 ‖x‖²` is convex (this includes convexity
of `D`, which the extended-valued definition forces). `ρ < 0` means `(-ρ)`-strongly convex. -/
def IsWeaklyConvexOn {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ConvexOn ℝ D (fun x => ψ x + ρ / 2 * ‖x‖ ^ 2)

/-- (2.6), p. 11: the Moreau envelope `ψ_lam(x) = min_y {ψ(y) + ‖y − x‖²/(2 lam)}`, the minimum over `dom ψ = D`
(outside `D`, `ψ = +∞` contributes nothing). Real infimum: junk `0` if `D = ∅` or the family is unbounded below;
every theorem carries hypotheses under which it is the attained minimum (Lemma 2.2). -/
noncomputable def moreauEnv {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨅ y : D, ψ y + 1 / (2 * lam) * ‖(y : EuclideanSpace ℝ (Fin d)) - x‖ ^ 2

/-- (2.6), p. 11: `p = prox_{lam ψ}(x)`, a minimizer over `D` of `y ↦ ψ(y) + ‖y − x‖²/(2 lam)`. -/
def IsProxPt {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (lam : ℝ)
    (x p : EuclideanSpace ℝ (Fin d)) : Prop :=
  p ∈ D ∧ ∀ y ∈ D, ψ p + 1 / (2 * lam) * ‖p - x‖ ^ 2 ≤ ψ y + 1 / (2 * lam) * ‖y - x‖ ^ 2

/-- `x₀ = x0`, `x_{t+1} = upd t x_t (ω t)` for `t < N`, frozen afterwards. -/
noncomputable def run {d : ℕ} {Ω : Type*} (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) {N : ℕ} (ω : Fin N → Ω) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => x0
  | t + 1 => if h : t < N then upd t (run upd x0 ω t) (ω ⟨t, h⟩) else run upd x0 ω t

end StochModelWC.ModelBased


