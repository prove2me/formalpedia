-- Prove2me | Definitions.Def_CursoEDO_Defs
-- name    : CursoEDO_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T15:15:33.405836+00:00
-- url     : https://prove2.me/theorems/117ac188-28ae-4e5b-a318-e2096470830b
-- title:
--   Lipschitz in the second variable; solution of a Cauchy problem
-- statement:
--   This item fixes the two basic notions used throughout the *Curso de EDO* series.
--
--   **Lipschitz with respect to the second variable.** Let $E_1, E_2, E_3$ be normed spaces,
--   $U \subseteq E_1 \times E_2$, $f : E_1\times E_2 \to E_3$ and $c \in \mathbb R$. We say that $f$
--   is Lipschitz in the second variable on $U$ with constant $c$ when $c > 0$ and
--
--   $$
--   \|f(z,y_1) - f(z,y_2)\| \;\le\; c\,\|y_1 - y_2\|
--   \qquad \text{for all } z,\ y_1,\ y_2 \text{ with } (z,y_1)\in U,\ (z,y_2)\in U .
--   $$
--
--   The point of the definition is that the constant $c$ does not depend on the first variable $z$.
--   This is Definição 2.1.1 of the source, with the constant exposed as a parameter instead of being
--   quantified existentially.
--
--   **Solution of a Cauchy problem.** Let $E$ be a real Banach space, $f$ a map assigning
--   $f(t,x) \in E$ to a time $t$ and a state $x$, $U \subseteq \mathbb R \times E$,
--   $t_0 \in \mathbb R$, $x_0 \in E$, $I \subseteq \mathbb R$ and $\varphi : \mathbb R \to E$. We say
--   $\varphi$ is a solution on $I$ of the Cauchy problem $x' = f(t,x)$, $x(t_0) = x_0$ with graph in
--   $U$ when all of the following hold:
--
--   1. $t_0 \in I$;
--   2. $\varphi(t_0) = x_0$;
--   3. $(t, \varphi(t)) \in U$ for every $t \in I$;
--   4. for every $t \in I$, $\varphi$ has derivative $f(t,\varphi(t))$ at $t$ relative to $I$.
--
--   Condition 4 is the relative (within $I$) derivative, so at an endpoint of an interval it is the
--   corresponding one-sided derivative — exactly the convention of Definição 1.0.1 of the source.
--   Condition 3 is the requirement that the graph of the solution stay inside the domain of $f$.
--
--   These two notions are the vocabulary in which the mission's goal theorem and its milestones are
--   stated, and they are intended to be reused by the later missions of this series.
--
--   **Formalization Note.** Solutions are modelled as total functions $\mathbb R \to E$ constrained
--   only on $I$; consequently uniqueness statements in this mission assert agreement of two solutions
--   on $I$, not equality of functions.
-- source:
--   Augusto Armando de Castro Junior, Curso de Equacoes Diferenciais Ordinarias, lecture notes, 06 January 2009, p. 34 Definicao 1.1.1 and p. 43 Definicao 2.1.1

import Mathlib

namespace CursoEDO

/-- Lipschitz with respect to the second variable, with an explicit constant `c > 0`
(Castro Júnior, *Curso de EDO*, Definição 2.1.1). -/
def LipschitzInSecondVar {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [NormedAddCommGroup E₃] (U : Set (E₁ × E₂)) (f : E₁ × E₂ → E₃) (c : ℝ) : Prop :=
  0 < c ∧ ∀ z : E₁, ∀ y₁ y₂ : E₂, (z, y₁) ∈ U → (z, y₂) ∈ U →
    ‖f (z, y₁) - f (z, y₂)‖ ≤ c * ‖y₁ - y₂‖

/-- `φ` is a solution, on the set `I`, of the Cauchy problem `dx/dt = f t x`, `x t₀ = x₀`,
with graph contained in `U` (Castro Júnior, *Curso de EDO*, Definição 1.0.1 / 1.1.1). -/
def IsCauchySolutionOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (U : Set (ℝ × E)) (t₀ : ℝ) (x₀ : E) (I : Set ℝ) (φ : ℝ → E) : Prop :=
  t₀ ∈ I ∧ φ t₀ = x₀ ∧ (∀ t ∈ I, (t, φ t) ∈ U) ∧
    ∀ t ∈ I, HasDerivWithinAt φ (f t (φ t)) I t

end CursoEDO


