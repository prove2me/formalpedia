-- Prove2me | Definitions.Def_ValuativeSYZ_cost_transform
-- name    : ValuativeSYZ_cost_transform
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T11:06:23.785605+00:00
-- url     : https://prove2.me/theorems/cb4c1aad-bb9e-4a2c-b026-1d3c2a7bf7a2
-- title:
--   Cost functions and the $c$-transform
-- statement:
--   This file fixes the conventions for the **cost function** and the **$c$-transform** used
--   throughout the mission (§3.2 of the source paper).
--
--   Let $X$ and $B$ be types and let $c \colon X \times B \to \mathbb{R}$ be a cost function,
--   written $c(x,p)$. For $\varphi \colon X \to \mathbb{R}$ and $\psi \colon B \to \mathbb{R}$ the two
--   $c$-transforms are
--   $$\varphi^{c}(p) \;=\; \sup_{x \in X}\big(c(x,p) - \varphi(x)\big), \qquad
--   \psi^{c}(x) \;=\; \sup_{p \in B}\big(c(x,p) - \psi(p)\big).$$
--   Both suprema are taken in the real numbers; no extended-real values are used, so every statement
--   that relies on a supremum being finite carries explicit boundedness hypotheses. A function is
--   called *bounded* here when its absolute value admits a uniform finite bound.
--
--   The class $P_c$ consists of those functions on $X$ which arise as the $c$-transform $\psi^{c}$ of
--   some **bounded** function $\psi$ on $B$; no continuity of $\psi$ is required. In the paper this is
--   the class of functions on the essential skeleton that are identified with continuous semipositive
--   potentials satisfying the domination property.
-- source:
--   Yang Li, *Valuative independence and metric SYZ conjecture*, arXiv:2605.00516v1 (1 May 2026), https://arxiv.org/abs/2605.00516, pp. 15, §3.2 (equation (10)) and the class $P_c$

import Mathlib

set_option autoImplicit false

namespace ValuativeSYZ

/-- A real-valued function is *bounded* if its absolute value admits a uniform bound.
This is the `L^∞` condition used for the `c`-transform in Yang Li,
*Valuative independence and metric SYZ conjecture*, §3.2. -/
def BddFun {α : Type*} (f : α → ℝ) : Prop := ∃ M : ℝ, ∀ a, |f a| ≤ M

/-- The `c`-transform of a function `φ : X → ℝ` on the base, with respect to a
cost function `c : X → B → ℝ`:  `φᶜ(p) = sup_x (c x p - φ x)`. -/
noncomputable def ctransform {X B : Type*} (c : X → B → ℝ) (φ : X → ℝ) : B → ℝ :=
  fun p => ⨆ x : X, (c x p - φ x)

/-- The `c`-transform of a function `ψ : B → ℝ` on the parameter space:
`ψᶜ(x) = sup_p (c x p - ψ p)`. -/
noncomputable def ctransformDual {X B : Type*} (c : X → B → ℝ) (ψ : B → ℝ) : X → ℝ :=
  fun x => ⨆ p : B, (c x p - ψ p)

/-- The class `P_c` of functions on `X` obtained as the `c`-transform of a bounded
function on the parameter space `B`. -/
def Pc {X B : Type*} (c : X → B → ℝ) : Set (X → ℝ) :=
  {φ | ∃ ψ : B → ℝ, BddFun ψ ∧ φ = ctransformDual c ψ}

end ValuativeSYZ


