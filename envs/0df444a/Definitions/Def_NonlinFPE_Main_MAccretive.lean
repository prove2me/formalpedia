-- Prove2me | Definitions.Def_NonlinFPE_Main_MAccretive
-- name    : NonlinFPE_Main_MAccretive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:47.281013+00:00
-- url     : https://prove2.me/theorems/9838f43d-ec08-4778-a8e8-5caa71c19362
-- title:
--   §3, p. 8 — m-accretive operators (3.3) and mild solutions (3.4)–(3.6) of du/dt + Au = 0 in a Banach space
-- statement:
--   Let $\mathcal X$ be a real normed space and $A$ a possibly multivalued operator on $\mathcal X$, given by its graph: $v \in Au$ means that the pair $(u,v)$ belongs to the graph, and $D(A) = \{u : Au \neq \emptyset\}$.
--
--   1. $A$ is **m-accretive** if, for every $\lambda > 0$, the range of $I + \lambda A$ is all of $\mathcal X$ (every $f$ is $u + \lambda v$ with $v \in Au$), and
--   $$\|u_1 - u_2\|_{\mathcal X} \le \|(u_1 + \lambda v_1) - (u_2 + \lambda v_2)\|_{\mathcal X}, \qquad v_1 \in Au_1,\ v_2 \in Au_2,\ \lambda > 0 .$$
--   The second condition is the contraction property (3.3) of the resolvent $(I+\lambda A)^{-1}$, and makes the resolvent single valued.
--
--   2. A **run of the implicit Euler scheme** (3.6) with step $h$ and $N$ steps is a sequence $u_h^0 = u_0, u_h^1, \dots, u_h^N$ with $u_h^i + hAu_h^i \ni u_h^{i-1}$ for $i = 1, \dots, N$.
--
--   3. A continuous $u : [0,\infty) \to \mathcal X$ is a **mild solution** of
--   $$\frac{du}{dt}(t) + Au(t) = 0,\quad t \ge 0, \qquad u(0) = u_0, \tag{3.2}$$
--   if for each $0 < T < \infty$ the step functions $u_h(t) = u_h^i$ for $t \in [ih, (i+1)h)$, $i = 0, \dots, N = [T/h]$, converge to $u(t)$ in $\mathcal X$ uniformly in $t \in [0,T]$ as $h \to 0$ ((3.4)–(3.5)).
--
--   These are the abstract objects of the Crandall–Liggett theory through which the paper solves the nonlinear Fokker–Planck equation in $L^1$.
--
--   **Formalization Note** The operator is a relation `A : X → X → Prop`, never a chosen resolvent. In the mild-solution definition, for every $T>0$ and $\varepsilon>0$ there is $h_0>0$ such that for each $h \in (0,h_0)$ a run of the scheme with $N = \lfloor T/h \rfloor$ exists and every such run satisfies $\|u(t) - u_h^{\lfloor t/h\rfloor}\| \le \varepsilon$ for $t \in [0,T]$. Requiring a run to exist keeps the notion from holding vacuously for an operator whose scheme cannot be started; $u(0) = u_0$ follows from the case $t = 0$. Time is $[0,\infty)$ as `ℝ≥0`.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §3, p. 8, (3.2)–(3.6)

import Mathlib

open scoped NNReal

namespace NonlinFPE.Main

/-- m-accretivity (3.3) of a possibly multivalued operator `A` on a real normed space `X`, given by
its graph: `A u v` means `v ∈ A u`, and `{u | ∃ v, A u v}` is the domain `D(A)`.
(1) Range condition: for every `λ > 0`, `R(I + λA) = X`, i.e. every `f` is `u + λ v` with `v ∈ A u`.
(2) Accretivity: `‖u₁ - u₂‖ ≤ ‖(u₁ + λ v₁) - (u₂ + λ v₂)‖` for all `λ > 0` and graph points; this is
(3.3) for the resolvent `(I + λA)⁻¹`, which (2) makes single valued, without choosing it. -/
def IsMAccretive {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : X → X → Prop) : Prop :=
  (∀ lam : ℝ, 0 < lam → ∀ f : X, ∃ u v, A u v ∧ u + lam • v = f) ∧
  (∀ lam : ℝ, 0 < lam → ∀ u₁ v₁ u₂ v₂ : X, A u₁ v₁ → A u₂ v₂ →
    ‖u₁ - u₂‖ ≤ ‖(u₁ + lam • v₁) - (u₂ + lam • v₂)‖)

/-- A run of the implicit Euler scheme (3.6) with step `h` and `N` steps:
`s 0 = u₀` and `s i + h A (s i) ∋ s (i - 1)` for `i = 1, …, N` (i.e. some `v ∈ A (s i)` has
`s i + h v = s (i - 1)`). Values `s i` for `i > N` are unconstrained. -/
def IsSchemeRun {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : X → X → Prop)
    (u₀ : X) (h : ℝ) (N : ℕ) (s : ℕ → X) : Prop :=
  s 0 = u₀ ∧ ∀ i : ℕ, 1 ≤ i → i ≤ N → ∃ v, A (s i) v ∧ s i + h • v = s (i - 1)

/-- Mild solution (3.4)–(3.6) of `du/dt + A u = 0`, `u(0) = u₀`: `u : [0, ∞) → X` is continuous and,
for every `0 < T < ∞`, the step functions `u_h(t) = u_h^i` on `[ih, (i+1)h)`, `N = ⌊T/h⌋`, converge
to `u` uniformly on `[0, T]` as `h → 0`. The scheme is required to have a run for every small `h`
(existence), and every run converges (there is one run when `A` is accretive). -/
def IsMildSolution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : X → X → Prop)
    (u₀ : X) (u : ℝ≥0 → X) : Prop :=
  Continuous u ∧
  ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
    (∃ s : ℕ → X, IsSchemeRun A u₀ h ⌊T / h⌋₊ s) ∧
    ∀ s : ℕ → X, IsSchemeRun A u₀ h ⌊T / h⌋₊ s →
      ∀ t : ℝ≥0, (t : ℝ) ≤ T → ‖u t - s ⌊(t : ℝ) / h⌋₊‖ ≤ ε

end NonlinFPE.Main


