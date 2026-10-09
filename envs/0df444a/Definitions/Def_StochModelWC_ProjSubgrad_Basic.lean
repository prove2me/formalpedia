-- Prove2me | Definitions.Def_StochModelWC_ProjSubgrad_Basic
-- name    : StochModelWC_ProjSubgrad_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:33:40.4427+00:00
-- url     : https://prove2.me/theorems/bdd08532-1dde-42d6-9f0e-b23db3463597
-- title:
--   Closed extended-valued functions, weak convexity, Moreau envelope, prox points, Fréchet subdifferential, the iterate run
-- statement:
--   Throughout, $E = \mathbb R^d$ is Euclidean space with the standard inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. An extended-valued function $\psi : \mathbb R^d \to \mathbb R \cup \{+\infty\}$ is described by its domain $D = \operatorname{dom}\psi = \{x : \psi(x) < \infty\}$ together with its finite values on $D$. This file introduces the basic objects of Davis–Drusvyatskiy, §2.
--
--   1. **Closedness.** $\psi$ is *closed* if its epigraph $\operatorname{epi}\psi = \{(x,t) \in \mathbb R^d \times \mathbb R : x \in D,\ \psi(x) \le t\}$ is a closed set (equivalently, $\psi$ is lower semicontinuous).
--   2. **Weak convexity.** For a real $\rho$, $\psi$ is *$\rho$-weakly convex* if
--   $$x \mapsto \psi(x) + \frac{\rho}{2}\|x\|^2$$
--   is a convex function; for an extended-valued $\psi$ this includes convexity of the domain $D$. A negative $\rho$ means $(-\rho)$-strong convexity.
--   3. **Moreau envelope and proximal point.** For $\lambda > 0$,
--   $$\psi_\lambda(x) = \min_{y}\Big\{\psi(y) + \frac{1}{2\lambda}\|y - x\|^2\Big\}, \qquad \operatorname{prox}_{\lambda\psi}(x) = \operatorname*{argmin}_{y}\Big\{\psi(y) + \frac{1}{2\lambda}\|y - x\|^2\Big\},$$
--   where the minimization runs over $D$ (points outside $D$ contribute $+\infty$). The predicate "$p$ is a proximal point of $\lambda\psi$ at $x$" means that $p \in D$ attains this minimum.
--   4. **Subdifferential.** For $x \in D$, $\partial\psi(x)$ is the set of $v$ with
--   $$\psi(y) \ge \psi(x) + \langle v, y - x\rangle + o(\|y - x\|) \quad \text{as } y \to x,$$
--   and $\partial\psi(x) = \emptyset$ for $x \notin D$ (the Fréchet, or regular, subdifferential).
--   5. **Iterate runs.** Given an update rule $(t, x, \xi) \mapsto \mathrm{upd}_t(x, \xi)$, a starting point $x_0$ and a finite sample path $(\xi_0, \dots, \xi_{N-1})$, the run is $x_{t+1} = \mathrm{upd}_t(x_t, \xi_t)$ for $t < N$, frozen afterwards.
--
--   These are the objects in which every statement of the mission is phrased. In §3.1 the regularizer is the indicator of a closed convex set $X$, so $\varphi = f + \delta_X$ is encoded by the domain $X$ and the values of $f$, and the stationarity measure is the gradient of its Moreau envelope $\varphi_{1/\bar\rho}(x) = \min_{y \in X}\{f(y) + \frac{\bar\rho}{2}\|y - x\|^2\}$.
--
--   **Formalization Note.** The envelope is a real infimum over the subtype $D$; it is a junk value $0$ when $D = \emptyset$ or the family is unbounded below, so every theorem using it carries hypotheses (closed, proper, weakly convex, $\lambda$ small) under which it is the attained minimum (Lemma 2.2). The subdifferential is the published regular subgradient `NonconvexSplitting.Shared.IsRegularSubgrad` applied to the $\overline{\mathbb R}$-valued lift that equals $\psi$ on $D$ and $+\infty$ off $D$. The parameter $\lambda$ is written `lam` because `λ` is a Lean keyword.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, pp. 7–8 (closed, weakly convex), p. 10 (subdifferential), p. 11 (2.6)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open MeasureTheory Filter Topology

namespace StochModelWC.ProjSubgrad

open NonconvexSplitting.Shared

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

open scoped Classical in
/-- p. 10: the (Fréchet) subdifferential of the extended-valued `ψ` encoded by `(D, ψ)`: the published
regular subgradient (`NonconvexSplitting.Shared.IsRegularSubgrad`) of its `EReal` lift, which is `ψ` on `D` and
`+∞` off `D`. So `v ∈ ∂ψ(x)` iff `x ∈ D` and `ψ(y) ≥ ψ(x) + ⟨v, y − x⟩ + o(‖y − x‖)` as `y → x`; `∂ψ(x) = ∅`
off `dom ψ`. -/
def frechetSubdiff {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d))) (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {v | IsRegularSubgrad (fun y => if y ∈ D then ((ψ y : ℝ) : EReal) else ⊤) x v}

/-- `x₀ = x0`, `x_{t+1} = upd t x_t (ω t)` for `t < N`, frozen afterwards. -/
noncomputable def run {d : ℕ} {Ω : Type*} (upd : ℕ → EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) {N : ℕ} (ω : Fin N → Ω) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => x0
  | t + 1 => if h : t < N then upd t (run upd x0 ω t) (ω ⟨t, h⟩) else run upd x0 ω t

end StochModelWC.ProjSubgrad


