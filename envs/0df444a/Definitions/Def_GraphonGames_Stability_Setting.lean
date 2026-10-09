-- Prove2me | Definitions.Def_GraphonGames_Stability_Setting
-- name    : GraphonGames_Stability_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T17:44:24.650177+00:00
-- url     : https://prove2.me/theorems/693bdb09-2f19-4669-9f87-b9e764a49691
-- title:
--   Graphon game setting: assumptions, operator, aggregate, cost, response, equilibrium
-- statement:
--   Players are indexed by $I=[0,1]$ with Lebesgue probability measure, and each action is a real number. A graphon $w:I\times I\to\mathbb R$ is measurable, symmetric, and square integrable. Its integral operator and norm are
--
--   $$
--   [Wg](x)=\int_I w(x,y)g(y)\,dy,\qquad
--   \|W\|=\sup_{\|g\|_{L^2}=1}\|Wg\|_{L^2}.
--   $$
--
--   Given a state map $b:\mathbb R\times\mathbb R\to\mathbb R$, a noise law $\mu_0$ on $\mathbb R$, and a function $f$, the state of a player taking action $a$ facing aggregate $z$ with noise $\xi$ is $X=b(a,z)+\xi$, and the expected cost is
--
--   $$
--   J(a,z)=\int_{\mathbb R} f\big(b(a,z)+\xi,\,a,\,z\big)\,\mu_0(d\xi).
--   $$
--
--   The standing assumptions are:
--
--   1. **Assumption 1** (constants $c_\alpha,c_z\ge0$): $|b(a,z)-b(a',z')|^2\le c_\alpha|a-a'|^2+c_z|z-z'|^2$ for all $a,z,a',z'$; and $\mu_0$ is a probability measure with $\int\xi^2\,\mu_0(d\xi)<\infty$ and mean $\int\xi\,\mu_0(d\xi)=0$.
--   2. **Assumption 4** (on a function $J$, constants $\ell_c>0$, $\ell_J\ge0$): for each $z$, $a\mapsto J(a,z)$ is continuously differentiable; for all $a,a',z$ and $\epsilon\in[0,1]$, $J(\epsilon a+(1-\epsilon)a',z)\le\epsilon J(a,z)+(1-\epsilon)J(a',z)-\tfrac{\ell_c}{2}\epsilon(1-\epsilon)|a-a'|^2$; and $|\partial_aJ(a,z')-\partial_aJ(a,z)|\le\ell_J|z'-z|$.
--   3. **Assumption 5** (constant $c_0>0$): $|b(a,z)|\le c_0$ for all $a,z$.
--
--   An aggregate for a profile $\alpha\in L^2(I)$ is a function $z\in L^2(I)$ with $z(x)=\int_I w(x,y)\,b(\alpha(y),z(y))\,dy$ for almost every $x$ (equation (6)). The best response $Bz$ to $z$ assigns to each player $x$ a minimizer of $a\mapsto J(a,z(x))$. A Nash equilibrium is a profile $\alpha\in L^2(I)$ having an aggregate $z$ such that, for almost every $x$, $J(\alpha(x),z(x))\le J(\beta,z(x))$ for every $\beta\in\mathbb R$.
--
--   These definitions give the common model for the aggregate, uniqueness, and graphon stability results.
--
--   **Formalization Note** Assumptions 1, 4, 5 and the cost $J$ are the shared declarations `GraphonGames.Existence.Asm1`, `Asm4`, `Asm5` and `cost`, imported from the shared module `GraphonGames.Existence.Setting`; this module declares the graphon, operator, aggregate, best response and equilibrium. Profiles and aggregates are represented by functions and identified almost everywhere. The equilibrium predicate uses the third, equivalent condition in Proposition 3.6, rather than a rich Fubini extension. The operator norm uses extended nonnegative reals; real constants use its finite value for graphons. The mean-zero clause of Assumption 1 is the paper's standing assumption on the noise (pp. 3 and 7). The best response is selected by classical choice; under Assumption 4 the minimizer exists and is unique, so the choice is never arbitrary.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, pp. 3, 7–11, 15, Assumptions 1, 4, 5, (1), (6), Proposition 3.6

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Stability

abbrev I := unitInterval

/-- Real-valued symmetric square-integrable graphons on the player interval. -/
def IsGraphon (w : I → I → ℝ) : Prop :=
  Measurable (Function.uncurry w) ∧
  (∀ x y, w x y = w y x) ∧
  MemLp (Function.uncurry w) 2 (volume : Measure (I × I))

/-- The integral operator associated with a graphon kernel. -/
noncomputable def graphonApply (w : I → I → ℝ) (g : I → ℝ) : I → ℝ :=
  fun x => ∫ y, w x y * g y

/-- The L²-to-L² operator norm, taken in the extended nonnegative reals. -/
noncomputable def opNorm (w : I → I → ℝ) : ℝ≥0∞ :=
  ⨆ (φ : I → ℝ) (_ : MemLp φ 2 volume ∧ eLpNorm φ 2 volume = 1),
    eLpNorm (graphonApply w φ) 2 volume

/-- Equation (6), with profiles represented by functions modulo a.e. equality. -/
def IsAggregate (w : I → I → ℝ) (b : ℝ → ℝ → ℝ)
    (α z : I → ℝ) : Prop :=
  MemLp z 2 volume ∧
  ∀ᵐ x ∂volume, z x = ∫ y, w x y * b (α y) (z y)

/-- The unique pointwise minimizer selected using classical choice. -/
noncomputable def bestResponse (J : ℝ → ℝ → ℝ) (z : I → ℝ) : I → ℝ :=
  fun x => Classical.epsilon (fun a => ∀ β, J a (z x) ≤ J β (z x))

/-- Nash equilibrium in the equivalent form of Proposition 3.6. -/
def IsNash (w : I → I → ℝ) (b : ℝ → ℝ → ℝ)
    (f : ℝ → ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (α : I → ℝ) : Prop :=
  MemLp α 2 volume ∧
  ∃ z, IsAggregate w b α z ∧
    ∀ᵐ x ∂volume, ∀ β : ℝ, GraphonGames.Existence.cost b f μ0 (α x) (z x) ≤ GraphonGames.Existence.cost b f μ0 β (z x)

end GraphonGames.Stability


