-- Prove2me | Definitions.Def_MarginalUtility_Model
-- name    : MarginalUtility_Model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:29:18.197983+00:00
-- url     : https://prove2.me/theorems/0484bd1c-0b0b-47fb-9001-e4caf4713c79
-- title:
--   Utility change $\Delta U$, marginal utility $\partial U/\partial g$, diminishing marginal utility $\partial^2 U/\partial g^2<0$
-- statement:
--   This file fixes the vocabulary of the section *Quantified marginal utility*.
--
--   1. **Change in utility.** For any set of states $S$, a utility $U:S\to\mathbb R$ and states $s_1,s_2\in S$,
--   $$\Delta U(s_1\to s_2)=U(s_2)-U(s_1).$$
--   2. **Marginal utility.** For a utility $U:\mathbb R\to\mathbb R$ of a single quantified variable $g$ (everything else held fixed, *c.p.*),
--   $$\frac{\partial U}{\partial g}(g)=U'(g),$$
--   the derivative of $U$ at $g$. (Lean's `deriv` returns $0$ where $U$ is not differentiable; every statement in this mission that uses marginal utility also assumes the differentiability it needs.)
--   3. **Diminishing marginal utility on $D\subseteq\mathbb R$.** $U$ is differentiable on $D$, its marginal utility $U'$ is differentiable on $D$, and
--   $$\frac{\partial^2 U}{\partial g^2}(g)<0\quad\text{for every } g\in D.$$
-- source:
--   Wikipedia, "Marginal utility" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Marginal_utility

import Mathlib

namespace MarginalUtility

/-- Change in utility when moving from state `s₁` to state `s₂`:
`ΔU = U(s₂) - U(s₁)`. -/
def utilityChange {S : Type*} (U : S → ℝ) (s₁ s₂ : S) : ℝ :=
  U s₂ - U s₁

/-- Marginal utility `∂U/∂g` of a utility function `U` of a single quantified variable `g`
(all other variables held fixed, *ceteris paribus*): the derivative of `U` at `g`. -/
noncomputable def marginalUtility (U : ℝ → ℝ) (g : ℝ) : ℝ :=
  deriv U g

/-- `U` has diminishing marginal utility on the set `D`: `U` is differentiable on `D`, its
marginal utility `∂U/∂g` is differentiable on `D`, and `∂²U/∂g² < 0` at every point of `D`. -/
def HasDiminishingMarginalUtility (U : ℝ → ℝ) (D : Set ℝ) : Prop :=
  DifferentiableOn ℝ U D ∧ DifferentiableOn ℝ (deriv U) D ∧
    ∀ g ∈ D, deriv (deriv U) g < 0

end MarginalUtility


