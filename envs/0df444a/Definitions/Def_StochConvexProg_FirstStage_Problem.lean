-- Prove2me | Definitions.Def_StochConvexProg_FirstStage_Problem
-- name    : StochConvexProg_FirstStage_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:35.151273+00:00
-- url     : https://prove2.me/theorems/e4ffed3f-6637-44cb-adb2-4ce8e45b1544
-- title:
--   The two-stage stochastic convex program: data, standing assumptions, the spaces X, U and the perturbation functional F (pp. 173–175)
-- statement:
--   This file fixes the model of Rockafellar and Wets' two-stage stochastic convex program.
--
--   Let $(S,\Sigma,\sigma)$ be a probability space. A first-stage decision $x_1\in\mathbb R^{n_1}$ is chosen subject to
--   $$x_1\in C_1,\qquad f_{1i}(x_1)\le 0\quad (i=1,\dots,m_1),$$
--   at cost $f_{10}(x_1)$; then $s\in S$ is observed and a recourse $x_2(s)\in\mathbb R^{n_2}$ is chosen subject to
--   $$x_2(s)\in C_2,\qquad f_{2i}(s,x_1,x_2(s))\le 0\quad (i=1,\dots,m_2),$$
--   at cost $f_{20}(s,x_1,x_2(s))$. The standing assumptions of the paper (p. 174) are part of the data:
--
--   1. $C_1\subseteq\mathbb R^{n_1}$ and $C_2\subseteq\mathbb R^{n_2}$ are convex, closed and nonempty;
--   2. $f_{10}, f_{1i}$ on $\mathbb R^{n_1}$ and $f_{20}(s,\cdot,\cdot), f_{2i}(s,\cdot,\cdot)$ on $\mathbb R^{n_1}\times\mathbb R^{n_2}$ are convex and finite everywhere;
--   3. for each $(x_1,x_2)$, $s\mapsto f_{2i}(s,x_1,x_2)$ is measurable, summable for $i=0$ and bounded for $i=1,\dots,m_2$.
--
--   The decision and perturbation spaces are $X=\mathbb R^{n_1}\times\mathcal L^\infty_{n_2}$ and $U=\mathbb R^{m_1}\times\mathcal L^\infty_{m_2}$. For $x=(x_1,x_2)\in X$ and $u=(u_1,u_2)\in U$, the point $x$ is *feasible for $u$* if
--   $$x_1\in C_1,\ \ f_{1i}(x_1)\le u_{1i}\ (i\le m_1),\qquad x_2(s)\in C_2,\ \ f_{2i}(s,x_1,x_2(s))\le u_{2i}(s)\ (i\le m_2)\ \text{ for almost every } s,$$
--   and the perturbation functional $F:X\times U\to\mathbb R\cup\{+\infty\}$ is
--   $$F(x,u)=\begin{cases} f_{10}(x_1)+\displaystyle\int_S f_{20}(s,x_1,x_2(s))\,\sigma(ds) & \text{if } x \text{ is feasible for } u,\\ +\infty & \text{otherwise.}\end{cases}$$
--   The original problem $\mathbf P$ is the minimization of $F(x,0)$ over $x\in X$.
--
--   Every other object of the mission (the integrands $F_1,F_2$, the first-stage functions $J$, $q$, $j$, the distance $\rho$) is built on this layer.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; the index $i=1,\dots,m$ is `Fin m` (Lean's `i` is the paper's $i+1$), and the cost functions $f_{10},f_{20}$ are separate fields. $\mathcal L^\infty_n$ is Mathlib's `Lp (Fin n → ℝ) ⊤ σ` (almost-everywhere classes). Convexity of $f_{20}(s,\cdot,\cdot)$ and $f_{2i}(s,\cdot,\cdot)$ is joint convexity on the product. "Bounded" for $f_{2i}(\cdot,x_1,x_2)$ is everywhere-bounded, as printed. $F$ takes values in `EReal`; the integral in $F$ is the Bochner integral, which is the true integral because $s\mapsto f_{20}(s,x_1,x_2(s))$ is summable for essentially bounded $x_2$ (p. 174). The probability-measure hypothesis is carried by each theorem, not by this structure.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), pp. 173–175, (1.1)–(1.5) and the standing assumptions on p. 174

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem

open MeasureTheory

namespace StochConvexProg.FirstStage

/-- Rockafellar–Wets (1976), pp. 173–174: the data of the two-stage stochastic convex program and the
standing assumptions "in force throughout the paper" (p. 174). Lean index `i : Fin m` is the paper's
`i + 1`; `f₁₀`, `f₂₀` are the cost functions (index 0). -/
structure Problem (S : Type*) [MeasurableSpace S] (σ : Measure S) (n₁ n₂ m₁ m₂ : ℕ) where
  C₁ : Set (Fin n₁ → ℝ)
  C₂ : Set (Fin n₂ → ℝ)
  f₁₀ : (Fin n₁ → ℝ) → ℝ
  f₁ : Fin m₁ → (Fin n₁ → ℝ) → ℝ
  f₂₀ : S → (Fin n₁ → ℝ) → (Fin n₂ → ℝ) → ℝ
  f₂ : Fin m₂ → S → (Fin n₁ → ℝ) → (Fin n₂ → ℝ) → ℝ
  C₁_convex : Convex ℝ C₁
  C₁_closed : IsClosed C₁
  C₁_nonempty : C₁.Nonempty
  C₂_convex : Convex ℝ C₂
  C₂_closed : IsClosed C₂
  C₂_nonempty : C₂.Nonempty
  f₁₀_convex : ConvexOn ℝ Set.univ f₁₀
  f₁_convex : ∀ i, ConvexOn ℝ Set.univ (f₁ i)
  f₂₀_convex : ∀ s, ConvexOn ℝ Set.univ (fun x : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) => f₂₀ s x.1 x.2)
  f₂_convex : ∀ i s, ConvexOn ℝ Set.univ (fun x : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) => f₂ i s x.1 x.2)
  f₂₀_measurable : ∀ x₁ x₂, Measurable (fun s => f₂₀ s x₁ x₂)
  f₂₀_integrable : ∀ x₁ x₂, Integrable (fun s => f₂₀ s x₁ x₂) σ
  f₂_measurable : ∀ i x₁ x₂, Measurable (fun s => f₂ i s x₁ x₂)
  f₂_bounded : ∀ i x₁ x₂, ∃ B : ℝ, ∀ s, |f₂ i s x₁ x₂| ≤ B

/-- (1.4)–(1.5), pp. 174–175: `x` satisfies the constraints perturbed by `u`, the second-stage ones
almost surely. -/
def Problem.Feasible {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x : StochConvexProg.Duality.XSpace σ n₁ n₂) (u : StochConvexProg.Duality.USpace σ m₁ m₂) : Prop :=
  x.1 ∈ pr.C₁ ∧ (∀ i, pr.f₁ i x.1 ≤ u.1 i) ∧
    ∀ᵐ s ∂σ, x.2 s ∈ pr.C₂ ∧ ∀ i, pr.f₂ i s x.1 (x.2 s) ≤ u.2 s i

/-- pp. 174–175: `F(x, u)` is the expected cost (1.3) if (1.4)–(1.5) hold, `+∞` otherwise. -/
noncomputable def Problem.F {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x : StochConvexProg.Duality.XSpace σ n₁ n₂) (u : StochConvexProg.Duality.USpace σ m₁ m₂) : EReal := by
  classical
  exact if pr.Feasible x u then ((pr.f₁₀ x.1 + ∫ s, pr.f₂₀ s x.1 (x.2 s) ∂σ : ℝ) : EReal) else ⊤

end StochConvexProg.FirstStage


