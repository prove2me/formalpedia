-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Convex_crit
-- name    : NonsmoothLojasiewicz_Convex_crit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:50:20.714869+00:00
-- url     : https://prove2.me/theorems/14d1d3ff-2dad-4fd7-a813-a8d8183c82b0
-- title:
--   Nonsmooth slope $m_f$ (4) and critical set $\mathrm{crit}\, f$ (Definition 2.11)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ and let $\partial f(x)$ be its limiting subdifferential at $x$ (Definition 2.10(ii) of the paper): the set of all cluster points of sequences $x_k^*\in\hat\partial f(x_k)$ with $(x_k,f(x_k))\to(x,f(x))$, where $\hat\partial f$ is the Fréchet subdifferential.
--
--   1. The **nonsmooth slope** of $f$ at $x$ is
--   $$m_f(x)=\inf\{\|x^*\|:\ x^*\in\partial f(x)\}\in[0,+\infty],$$
--   with $m_f(x)=+\infty$ whenever $\partial f(x)=\emptyset$.
--   2. The set of (generalized) **critical points** of $f$ is
--   $$\operatorname{crit} f=\{x\in\mathbb R^n:\ 0\in\partial f(x)\}.$$
--
--   The slope replaces $\|\nabla f\|$ in the nonsmooth Łojasiewicz inequality, and $\operatorname{crit} f$ is the set around which that inequality is stated.
--
--   **Formalization Note** The limiting subdifferential is the published definition `NonconvexSplitting.Shared.LimitingSubdiff`. The slope takes values in `ℝ≥0∞`, where the infimum over the empty set is $+\infty$.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211, equation (4) and Definition 2.11

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open scoped ENNReal NNReal

namespace NonsmoothLojasiewicz.Convex

/-- The nonsmooth slope (4) of Bolte–Daniilidis–Lewis (p. 1211):
`m_f(x) = inf {‖x*‖ : x* ∈ ∂f(x)}`, with `∂f` the limiting subdifferential (Definition 2.10(ii)).
It takes values in `[0, +∞]`; the infimum over the empty set is `+∞`, which is the page's
"`m_f(x) = +∞` whenever `∂f(x) = ∅`". -/
noncomputable def slope {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (x : X) : ℝ≥0∞ :=
  ⨅ v ∈ NonconvexSplitting.Shared.LimitingSubdiff f x, (‖v‖₊ : ℝ≥0∞)

/-- Definition 2.11 (p. 1211): the set of (generalized) critical points
`crit f = {x : 0 ∈ ∂f(x)}`, with `∂f` the limiting subdifferential. -/
def crit {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) : Set X :=
  {x | (0 : X) ∈ NonconvexSplitting.Shared.LimitingSubdiff f x}

end NonsmoothLojasiewicz.Convex


