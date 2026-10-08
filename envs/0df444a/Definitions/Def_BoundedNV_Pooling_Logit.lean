-- Prove2me | Definitions.Def_BoundedNV_Pooling_Logit
-- name    : BoundedNV_Pooling_Logit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:52:14.090675+00:00
-- url     : https://prove2.me/theorems/5d4ab3b1-4e58-467c-8939-a520dd7e1d84
-- title:
--   Eqs. (2), (4), pp. 571–572 — continuous logit choice law
-- statement:
--   A decision maker chooses a real quantity from a decision domain $S$ with utility $u$ and bounded-rationality parameter $\beta>0$. The **logit density** at $y$ is
--
--   $$
--   \psi(y)=\mathbf 1_S(y)\frac{e^{u(y)/\beta}}{\int_S e^{u(v)/\beta}\,dv}.
--   $$
--
--   Its choice distribution is $\Psi(y)=\int_{-\infty}^{y}\psi(v)\,dv$. For a measurable payoff $g$, its logit expectation is $\mathbb E[g(Y)]=\int_{\mathbb R}g(y)\psi(y)\,dy$.
--
--   These definitions supply the common choice model used by the invariance lemmas and Proposition 7. They represent a probability law when the normalizing integral is finite and positive.
--
--   **Formalization Note** The density is zero outside $S$. In Lean, an integral of a nonintegrable function has a default value, so the subsequent statements require a genuine normalizer or use positive newsvendor costs that ensure one.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, pp. 571–572 (PDF 6–7), eqs. (2), (4)

import Mathlib

open MeasureTheory

namespace BoundedNV.Pooling

/-- Equation (2): the logit choice density on the decision domain `S`. -/
noncomputable def logitDensity (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (y : ℝ) : ℝ :=
  S.indicator (fun y => Real.exp (u y / β) / ∫ v in S, Real.exp (u v / β)) y

/-- The choice distribution associated with the logit density, p. 571. -/
noncomputable def logitCDF (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (y : ℝ) : ℝ :=
  ∫ v in Set.Iic y, logitDensity S u β v

/-- Expectation of `g` under the logit choice distribution. -/
noncomputable def logitExp (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ y, g y * logitDensity S u β y

end BoundedNV.Pooling


