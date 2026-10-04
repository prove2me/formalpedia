-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
-- name    : NonsmoothLojasiewicz_Continuous_slope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:50:21.110272+00:00
-- url     : https://prove2.me/theorems/ddb596ca-3195-40e4-8d4a-0b3529e1341f
-- title:
--   Nonsmooth slope $m_f$ (4) and critical points $\mathrm{crit}\, f$ (Definition 2.11)
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$ and let $\partial f(x)$ denote its **limiting subdifferential** at $x$: the set of all limits $x^*$ of sequences $x^*_k \in \hat\partial f(x_k)$ of Fréchet subgradients, taken along $x_k \to x$ with $f(x_k) \to f(x)$.
--
--   1. The **nonsmooth slope** of $f$ at $x$ is
--   $$
--   m_f(x) := \inf\{\|x^*\| : x^* \in \partial f(x)\} \in [0, +\infty],
--   $$
--   with $m_f(x) = +\infty$ whenever $\partial f(x) = \emptyset$.
--   2. A point $a$ is a (generalized) **critical point** of $f$ if $0 \in \partial f(a)$; the set of critical points is
--   $$
--   \operatorname{crit} f := \{x \in \mathbb{R}^n : 0 \in \partial f(x)\}.
--   $$
--
--   The slope replaces the norm of the gradient in the Łojasiewicz inequality, and critical points are the points around which that inequality is a statement about the behaviour of $f$ near its critical values.
--
--   **Formalization Note.** The limiting subdifferential is the published `NonconvexSplitting.Shared.LimitingSubdiff`. The slope takes values in `ℝ≥0∞`, where the infimum over the empty set is `⊤`, which is the paper's convention $m_f(x) = +\infty$ when $\partial f(x) = \emptyset$. The space is `EuclideanSpace ℝ (Fin n)` and `f` takes values in `EReal`.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211 (PDF p. 7), equation (4) and Definition 2.11

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- The nonsmooth slope (4) of Bolte–Daniilidis–Lewis (p. 1211):
`m_f(x) = inf {‖x*‖ : x* ∈ ∂f(x)}`, where `∂f` is the limiting subdifferential (Def. 2.10(ii)).
Valued in `ℝ≥0∞`, so that the empty infimum is `⊤`: `m_f(x) = +∞` whenever `∂f(x) = ∅`. -/
noncomputable def slope {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨅ v ∈ NonconvexSplitting.Shared.LimitingSubdiff f x, (‖v‖₊ : ℝ≥0∞)

/-- Definition 2.11 (p. 1211): the set of (generalized) critical points
`crit f = {x : 0 ∈ ∂f(x)}`, with `∂f` the limiting subdifferential. -/
def crit {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (0 : EuclideanSpace ℝ (Fin n)) ∈ NonconvexSplitting.Shared.LimitingSubdiff f x}

end NonsmoothLojasiewicz.Continuous


