-- Prove2me | Definitions.Def_SSDConstraint_Optimality_Problem
-- name    : SSDConstraint_Optimality_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T07:47:10.598481+00:00
-- url     : https://prove2.me/theorems/0210cc04-efb3-443a-bedf-f400cda1c89e
-- title:
--   Problem (3.1)–(3.3): data, feasibility, optimality, uniform dominance (Def. 4.1), the class $\mathcal U_1$ and the Lagrangian (4.1)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\mathcal L^1(\Omega,\mathcal F,P)$ the space of integrable random variables. For $X\in\mathcal L^1$ and $\eta\in\mathbb R$ write
--   $$F_2(X;\eta)=\int_{-\infty}^{\eta}P[X\le\alpha]\,d\alpha,$$
--   the second-order shortfall function (2.1); $X\succeq_{(2)}Y$ means $F_2(X;\eta)\le F_2(Y;\eta)$ for all $\eta\in\mathbb R$, and $A_2(Y)=\{X\in\mathcal L^1: X\succeq_{(2)}Y\}$.
--
--   The **problem data** consist of a reference outcome $Y\in\mathcal L^1$, a convex closed set $C\subseteq\mathcal L^1$, a functional $f$ that is concave and continuous on $C$, and an interval $[a,b]$. The problem is
--   $$\max f(X)\quad\text{subject to}\quad \mathbb E[(\eta-X)_+]\le\mathbb E[(\eta-Y)_+]\ \text{ for all }\eta\in[a,b],\qquad X\in C. \tag{3.1–3.3}$$
--
--   1. $X$ is **feasible** if $X\in C$ and the constraint (3.2) holds; it is an **optimal solution** if it is feasible and $f(X')\le f(X)$ for every feasible $X'$.
--   2. The problem satisfies the **uniform dominance condition** (Definition 4.1) if there is $\tilde X\in C$ with $\inf_{\eta\in[a,b]}\{F_2(Y;\eta)-F_2(\tilde X;\eta)\}>0$.
--   3. $\mathcal U_1$ is the set of functions $u:\mathbb R\to\mathbb R$ that are concave and nondecreasing, satisfy $u(t)=0$ for $t\ge b$, and satisfy $u(t)=u(a)+c(t-a)$ for all $t\le a$ with some constant $c\ge0$.
--   4. The **Lagrangian** (4.1) is $L(X,u)=f(X)+\mathbb E[u(X)]-\mathbb E[u(Y)]$.
--
--   These objects are the model of Dentcheva and Ruszczyński's optimality theory: the multipliers of the dominance constraint (3.2) are the functions of $\mathcal U_1$, i.e. concave nondecreasing utility functions.
--
--   **Formalization Note** Outcomes are elements of Mathlib's $L^1$ space `Ω →₁[P] ℝ`; $F_2$ is the published `DualSSD.Shared.secondPerformance` applied to a representative (it depends only on the law). The paper prints $c>0$ in the definition of $\mathcal U_1$; this is corrected to $c\ge0$, because with $c>0$ Theorem 4.2 fails whenever the constraint is slack at the optimum (the multiplier must then be $u=0$), and the paper itself calls $\mathcal U_1$ a convex cone, which must contain $0$. Definition 4.1's infimum is encoded as "bounded below on $[a,b]$ by some $\varepsilon>0$", which is equivalent and avoids a real infimum. $f$ is a total function on $\mathcal L^1$, but only its values on $C$ enter. No relation between $a$ and $b$ is assumed, as on the page.
-- source:
--   Dentcheva and Ruszczyński, Optimization with stochastic dominance constraints, preprint dated December 27, 2002 (SPEPS; published SIAM J. Optim. 14(2), 2003), p. 2 (standing assumptions after (1.4)), pp. 3–5 ((2.1), (2.4), (2.5)), p. 6 ((3.1)–(3.3)), p. 8 (Definition 4.1, the set U_1, (4.1))

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

namespace SSDConstraint.Optimality

open MeasureTheory

/-- Dentcheva–Ruszczyński (2002 preprint), (2.1), p. 3: the second-order shortfall function
`F₂(X; η) = ∫_{-∞}^η P[X ≤ α] dα` of an integrable random variable `X ∈ L¹(Ω, ℱ, P)`, evaluated on a
representative of the `L¹` class. It is the published `DualSSD.Shared.secondPerformance`; it depends
only on the law of `X`, hence not on the representative. -/
noncomputable abbrev F2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω →₁[P] ℝ) (η : ℝ) :
    ℝ :=
  DualSSD.Shared.secondPerformance P (⇑X) η

/-- (2.5) with `k = 2`, p. 4 and p. 5: `A₂(Y) = {X ∈ L¹(Ω, ℱ, P) : X ⪰₍₂₎ Y}`, where `X ⪰₍₂₎ Y` is
(2.3)–(2.4): `F₂(X; η) ≤ F₂(Y; η)` for all `η ∈ ℝ` (the published `DualSSD.Shared.SSD`). -/
def A2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω →₁[P] ℝ) : Set (Ω →₁[P] ℝ) :=
  {X | DualSSD.Shared.SSD P (⇑X) (⇑Y)}

/-- The data of problem (3.1)–(3.3) (pp. 2 and 6), with every standing assumption of p. 2 as a field:
the reference outcome `Y ∈ L¹(Ω, ℱ, P)`, the feasible set `C ⊆ L¹(Ω, ℱ, P)`, convex and closed, the
objective `f`, concave and continuous on `C` (only its values on `C` matter), and the interval
`[a, b]` on which the dominance relation is enforced. No relation between `a` and `b` is assumed. -/
structure Problem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The feasible set `C`. -/
  C : Set (Ω →₁[P] ℝ)
  C_convex : Convex ℝ C
  C_closed : IsClosed C
  /-- The objective functional `f`. -/
  f : (Ω →₁[P] ℝ) → ℝ
  f_concave : ConcaveOn ℝ C f
  f_cont : ContinuousOn f C
  /-- The reference outcome `Y`. -/
  Y : Ω →₁[P] ℝ
  /-- The interval `[a, b]` of (3.2). -/
  a : ℝ
  b : ℝ

namespace Problem

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Feasibility for (3.1)–(3.3), p. 6: `X ∈ C` (3.3) and the dominance constraint (3.2) in its printed
expectation form, `𝔼[(η − X)₊] ≤ 𝔼[(η − Y)₊]` for all `η ∈ [a, b]`. -/
def Feasible (pr : Problem Ω P) (X : Ω →₁[P] ℝ) : Prop :=
  X ∈ pr.C ∧ ∀ η ∈ Set.Icc pr.a pr.b, ∫ ω, max (η - X ω) 0 ∂P ≤ ∫ ω, max (η - pr.Y ω) 0 ∂P

/-- An optimal solution of (3.1)–(3.3): a feasible `X̂` with `f(X) ≤ f(X̂)` for every feasible `X`. -/
def IsOptimal (pr : Problem Ω P) (X : Ω →₁[P] ℝ) : Prop :=
  pr.Feasible X ∧ ∀ X', pr.Feasible X' → pr.f X' ≤ pr.f X

/-- DEFINITION 4.1, p. 8 (uniform dominance condition): there is `X̃ ∈ C` with
`inf_{η ∈ [a, b]} {F₂(Y; η) − F₂(X̃; η)} > 0`, written as "bounded below on `[a, b]` by some `ε > 0`". -/
def UniformDominance (pr : Problem Ω P) : Prop :=
  ∃ Xt ∈ pr.C, ∃ ε > 0, ∀ η ∈ Set.Icc pr.a pr.b, ε ≤ F2 P pr.Y η - F2 P Xt η

/-- The Lagrangian (4.1), p. 8: `L(X, u) = f(X) + 𝔼[u(X)] − 𝔼[u(Y)]`. -/
noncomputable def lagrangian (pr : Problem Ω P) (X : Ω →₁[P] ℝ) (u : ℝ → ℝ) : ℝ :=
  pr.f X + ∫ ω, u (X ω) ∂P - ∫ ω, u (pr.Y ω) ∂P

end Problem

/-- The multiplier class `𝒰₁`, p. 8: `u : ℝ → ℝ` concave and nondecreasing, `u(t) = 0` for `t ≥ b`, and
`u(t) = u(a) + c(t − a)` for all `t ≤ a`, with some constant `c ≥ 0`. The page prints `c > 0`; under
that reading Theorem 4.2 is false (the multiplier of a slack constraint is `u = 0`), and the page itself
calls `𝒰₁` a (closed) convex cone, which requires `0 ∈ 𝒰₁`; `c ≥ 0` is the corrected condition. -/
def U1 (a b : ℝ) : Set (ℝ → ℝ) :=
  {u | ConcaveOn ℝ Set.univ u ∧ Monotone u ∧ (∀ t, b ≤ t → u t = 0) ∧
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t ≤ a, u t = u a + c * (t - a)}

end SSDConstraint.Optimality


