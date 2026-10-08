-- Prove2me | Definitions.Def_PDASNewton_FunSpace_Setting
-- name    : PDASNewton_FunSpace_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:03.374086+00:00
-- url     : https://prove2.me/theorems/56a23d36-f70b-4b10-a065-b88e2e287802
-- title:
--   Definition 1, (4.1), (4.2), §4 algorithm, pp. 2, 11–12 — slanting functions, superlinear convergence, G_m, the L² system and the L² primal-dual active set step
-- statement:
--   This module fixes the vocabulary of the infinite-dimensional part of Hintermüller, Ito and Kunisch. The paper writes $A$ for an operator and calligraphic $\mathcal{A}$, $\mathcal{I}$ for the active and inactive sets; in Lean the operator is `A` and the sets appear only through the pointwise conditions that define them.
--
--   Items 1 and 2 are the shared definitions `PDASNewton.Local.IsSlantingFunction` and `PDASNewton.Local.ConvergesSuperlinearly`, imported from `Definitions.Def_PDASNewton_Local_Setting`; items 3–7 are declared in this module.
--
--   1. **Slanting function** (Definition 1, p. 2). Let $X$, $Z$ be real normed spaces, $F : X \to Z$, $G : X \to \mathcal{L}(X, Z)$ and $U \subseteq X$. $G$ is a slanting function for $F$ in $U$ if for every $x \in U$
--   $$\lim_{h \to 0} \frac{1}{\|h\|}\,\|F(x+h) - F(x) - G(x+h)h\| = 0. \tag{A}$$
--   $F$ is slantly differentiable in $U$ when such a $G$ exists. No boundedness of $\{G(x) : x \in U\}$ is required.
--
--   2. **Superlinear convergence.** A sequence $x_k \to x^*$ converges superlinearly if $x_k \to x^*$ and, for every $\eta > 0$, eventually $\|x_{k+1} - x^*\| \le \eta\,\|x_k - x^*\|$.
--
--   3. **The candidate slanting function $G_m$** (4.1), p. 11. For a fixed $\delta \in \mathbb{R}$, $G_m(y)(x) = g_\delta(y(x))$ with
--   $$g_\delta(z) = \begin{cases} 1 & z > 0,\\ 0 & z < 0,\\ \delta & z = 0.\end{cases}$$
--
--   4. **Property (A) for $\max(0,\cdot) : L^q \to L^p$ with $G_m$.** On a measure space $(\Omega, \mu)$, for exponents $p, q$ and $y : \Omega \to \mathbb{R}$: for every $\varepsilon > 0$ there is $\eta > 0$ such that every $h \in L^q$ with $\|h\|_{L^q} < \eta$ satisfies
--   $$\|\max(0, y+h) - \max(0, y) - G_m(y+h)\,h\|_{L^p} \le \varepsilon\,\|h\|_{L^q}.$$
--
--   5. **System (4.2)**, p. 12. For $A \in \mathcal{L}(L^2(\Omega))$, $f, \psi \in L^2(\Omega)$ and $c \in \mathbb{R}$, a pair $(y, \lambda) \in L^2 \times L^2$ solves (4.2) if
--   $$Ay + \lambda = f, \qquad \lambda - \max(0, \lambda + c(y - \psi)) = 0 \ \text{ a.e.}$$
--
--   6. **One step of the primal-dual active set algorithm in $L^2(\Omega)$** (steps (ii)–(iii), p. 12). With $\mathcal{A} = \{x : \lambda(x) + c(y(x) - \psi(x)) > 0\}$ and $\mathcal{I} = \Omega \setminus \mathcal{A}$, the pair $(y', \lambda')$ follows $(y, \lambda)$ if
--   $$Ay' + \lambda' = f, \qquad y' = \psi \text{ a.e. on } \mathcal{A}, \qquad \lambda' = 0 \text{ a.e. on } \mathcal{I}.$$
--
--   7. **Run.** Sequences $(y^k, \lambda^k)_{k \ge 0}$ in $L^2 \times L^2$, with free initial pair, such that every $(y^{k+1}, \lambda^{k+1})$ follows $(y^k, \lambda^k)$.
--
--   These objects are the vocabulary of Theorem 1.1, Proposition 4.1 and Theorem 4.1.
--
--   **Formalization Note** $L^p(\Omega)$ is Mathlib's `Lp ℝ p μ` on an arbitrary measure space; the theorems add a finite measure. Pointwise conditions on $L^p$ classes are stated almost everywhere on representatives, since the active set of an $L^2$ iterate is defined only up to a null set. The $L^p$ norm in item 4 is Mathlib's `eLpNorm`, valued in $[0, \infty]$; membership $h \in L^q$ is `MemLp h q μ`. The algorithm is a relation: step (iv)'s "Stop" is not modelled and a run is infinite.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 2 Definition 1 and (A); p. 3 proof of Theorem 1.1 (superlinear convergence); p. 11 (4.1); p. 12 (4.2) and the primal-dual active set algorithm in L²(Ω)

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting

namespace PDASNewton.FunSpace

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal

/-- The scalar function behind the candidate slanting function `G_m` of (4.1), p. 11:
`G_m(y)(x) = gm δ (y x)`, equal to `1` if `y x > 0`, `0` if `y x < 0` and `δ` if `y x = 0`. -/
noncomputable def gm (δ : ℝ) (z : ℝ) : ℝ :=
  if 0 < z then 1 else if z < 0 then 0 else δ

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Property (A) of Definition 1 for `max(0, ·) : L^q(Ω) → L^p(Ω)` at `y` with the candidate
slanting function `G_m` of (4.1), written on functions: for every `ε > 0` there is `η > 0` such
that every `h ∈ L^q` with `‖h‖_{L^q} < η` satisfies
`‖max(0, y + h) - max(0, y) - G_m(y + h) h‖_{L^p} ≤ ε ‖h‖_{L^q}`. -/
def MaxSlantingAt (μ : Measure α) (p q : ℝ≥0∞) (δ : ℝ) (y : α → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ h : α → ℝ, MemLp h q μ →
    eLpNorm h q μ < ENNReal.ofReal η →
    eLpNorm (fun x => max 0 (y x + h x) - max 0 (y x) - gm δ (y x + h x) * h x) p μ ≤
      ENNReal.ofReal ε * eLpNorm h q μ

/-- System (4.2), p. 12, with the max-operation pointwise a.e.:
`A y + λ = f` in `L²` and `λ - max(0, λ + c (y - ψ)) = 0` a.e. -/
def IsSolution (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f ψ : Lp ℝ 2 μ) (c : ℝ)
    (y lam : Lp ℝ 2 μ) : Prop :=
  A y + lam = f ∧ ∀ᵐ x ∂μ, lam x - max 0 (lam x + c * (y x - ψ x)) = 0

/-- One iteration (ii)–(iii) of the primal-dual active set algorithm in `L²(Ω)`, p. 12:
with `𝓐 = {x : λ(x) + c (y(x) - ψ(x)) > 0}` and `𝓘 = Ω \ 𝓐`, the next iterate satisfies
`A y' + λ' = f`, `y' = ψ` a.e. on `𝓐` and `λ' = 0` a.e. on `𝓘`. -/
def IsStep (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f ψ : Lp ℝ 2 μ) (c : ℝ)
    (y lam y' lam' : Lp ℝ 2 μ) : Prop :=
  A y' + lam' = f ∧
  (∀ᵐ x ∂μ, 0 < lam x + c * (y x - ψ x) → y' x = ψ x) ∧
  (∀ᵐ x ∂μ, lam x + c * (y x - ψ x) ≤ 0 → lam' x = 0)

/-- A run of the algorithm: every consecutive pair of iterates is related by one step.
The initial pair `(y 0, lam 0)` is free; step (iv)'s "Stop" is not modelled. -/
def IsRun (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f ψ : Lp ℝ 2 μ) (c : ℝ)
    (y lam : ℕ → Lp ℝ 2 μ) : Prop :=
  ∀ k, IsStep A f ψ c (y k) (lam k) (y (k + 1)) (lam (k + 1))

end PDASNewton.FunSpace


