-- Prove2me | Definitions.Def_StochConvexProg_Duality_Problem
-- name    : StochConvexProg_Duality_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:56.350133+00:00
-- url     : https://prove2.me/theorems/554968d7-4d8e-42dc-b65e-a54286713594
-- title:
--   The two-stage stochastic convex program: data, standing assumptions, the spaces X, U and the perturbation functional F (pp. 173–175)
-- statement:
--   Rockafellar and Wets study the following two-stage decision problem. First a vector $x_1\in\mathbb R^{n_1}$ is chosen subject to
--   $$x_1\in C_1,\qquad f_{1i}(x_1)\le 0\quad(i=1,\dots,m_1),$$
--   at cost $f_{10}(x_1)$. Then an outcome $s$ of a probability space $(S,\Sigma,\sigma)$ is observed, and a vector $x_2(s)\in\mathbb R^{n_2}$ is chosen subject to
--   $$x_2(s)\in C_2,\qquad f_{2i}(s,x_1,x_2(s))\le 0\quad(i=1,\dots,m_2),$$
--   at cost $f_{20}(s,x_1,x_2(s))$. The total expected cost is
--   $$f_{10}(x_1)+\int_S f_{20}(s,x_1,x_2(s))\,\sigma(ds).$$
--
--   **Standing assumptions** (in force throughout the paper): $C_1\subseteq\mathbb R^{n_1}$ and $C_2\subseteq\mathbb R^{n_2}$ are convex, closed and nonempty; the functions $f_{1i}$ on $\mathbb R^{n_1}$ and $f_{2i}(s,\cdot,\cdot)$ on $\mathbb R^{n_1}\times\mathbb R^{n_2}$ ($i=0,1,\dots$) are convex and finite everywhere; for each $(x_1,x_2)$ the functions $s\mapsto f_{2i}(s,x_1,x_2)$ are measurable, summable for $i=0$ and bounded for $i=1,\dots,m_2$.
--
--   **Spaces.** $X=\mathbb R^{n_1}\times\mathcal L^\infty_{n_2}$ (decisions $x=(x_1,x_2)$) and $U=\mathbb R^{m_1}\times\mathcal L^\infty_{m_2}$ (perturbations $u=(u_1,u_2)$), where $\mathcal L^p_n$ is the Lebesgue space of $\mathbb R^n$-valued functions on $(S,\Sigma,\sigma)$.
--
--   **Perturbation functional.** $x$ is *feasible for $u$* if
--   $$x_1\in C_1,\quad f_{1i}(x_1)\le u_{1i}\ (i=1,\dots,m_1),\qquad\text{and almost surely}\quad x_2(s)\in C_2,\quad f_{2i}(s,x_1,x_2(s))\le u_{2i}(s)\ (i=1,\dots,m_2).$$
--   Then $F:X\times U\to\mathbb R\cup\{+\infty\}$ is the expected cost above if $x$ is feasible for $u$, and $+\infty$ otherwise. The original problem $\mathbf P$ minimizes $F(x,0)$ over $x\in X$; $\mathbf P(u)$ minimizes $F(x,u)$.
--
--   This is the model on which every statement of the mission is built.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`; the constraint indices $i=1,\dots,m$ are `Fin m`, so Lean's `i` is the paper's $i+1$, and the cost functions $f_{10},f_{20}$ are separate fields. $\mathcal L^\infty$ is Mathlib's `Lp _ ⊤ σ` (almost-everywhere classes), so the second-stage constraints are stated almost surely, as in the paper. $\mathbb R\cup\{+\infty\}$ is `EReal`. The integral in $F$ is the Bochner integral of a real function; for $x_2\in\mathcal L^\infty$ this function is summable (the claim on p. 174, a milestone of this mission), so the integral is the true expected cost. The boundedness of $f_{2i}(\cdot,x_1,x_2)$ is stated everywhere, as printed. The probability-measure hypothesis is carried by each theorem, not by the structure.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), pp. 173–175, (1.1)–(1.5) and the standing assumptions on p. 174

import Mathlib

open MeasureTheory

namespace StochConvexProg.Duality

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

/-- p. 174: `X = Rⁿ¹ × ℒ^∞_{n₂}`. -/
abbrev XSpace {S : Type*} [MeasurableSpace S] (σ : Measure S) (n₁ n₂ : ℕ) :=
  (Fin n₁ → ℝ) × Lp (Fin n₂ → ℝ) ⊤ σ

/-- p. 174: `U = R^{m₁} × ℒ^∞_{m₂}`. -/
abbrev USpace {S : Type*} [MeasurableSpace S] (σ : Measure S) (m₁ m₂ : ℕ) :=
  (Fin m₁ → ℝ) × Lp (Fin m₂ → ℝ) ⊤ σ

/-- (1.4)–(1.5), pp. 174–175: `x` satisfies the constraints perturbed by `u`, the second-stage ones
almost surely. -/
def Problem.Feasible {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x : XSpace σ n₁ n₂) (u : USpace σ m₁ m₂) : Prop :=
  x.1 ∈ pr.C₁ ∧ (∀ i, pr.f₁ i x.1 ≤ u.1 i) ∧
    ∀ᵐ s ∂σ, x.2 s ∈ pr.C₂ ∧ ∀ i, pr.f₂ i s x.1 (x.2 s) ≤ u.2 s i

/-- pp. 174–175: `F(x, u)` is the expected cost (1.3) if (1.4)–(1.5) hold, `+∞` otherwise. -/
noncomputable def Problem.F {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x : XSpace σ n₁ n₂) (u : USpace σ m₁ m₂) : EReal := by
  classical
  exact if pr.Feasible x u then ((pr.f₁₀ x.1 + ∫ s, pr.f₂₀ s x.1 (x.2 s) ∂σ : ℝ) : EReal) else ⊤

end StochConvexProg.Duality


