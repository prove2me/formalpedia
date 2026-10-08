-- Prove2me | Definitions.Def_BalkemaDeHaan_FiniteT_ResidualLife
-- name    : BalkemaDeHaan_FiniteT_ResidualLife
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:05.073985+00:00
-- url     : https://prove2.me/theorems/3afc8dd5-a9d6-4f41-bbcc-a92f744eaac5
-- title:
--   The residual life d.f. F_t(x) = P{X − t ≤ x | X > t}, a positive differentiable density, and a(t) = (1 − F(t))/F′(t)
-- statement:
--   Let $X$ be a real random variable with law $\mu$ and distribution function $F(x) = \mu((-\infty, x])$. The **residual life distribution function** at age $t$ is
--   $$
--   F_t(x) = P\{X - t \le x \mid X > t\} = \frac{\mu((t, t+x])}{\mu((t, \infty))},
--   $$
--   which vanishes for $x < 0$. For a norming $a(t) > 0$, $P\{(X-t)/a(t) \le x \mid X > t\} = F_t(x\,a(t))$.
--
--   For $t_0 \in \mathbb R$ and functions $f, f'$, the predicate "$F$ has a positive, differentiable density $F' = f$ for $t \ge t_0$" means: for every $t \ge t_0$, $F$ has derivative $f(t)$ at $t$ relative to $[t_0, \infty)$, $f(t) > 0$, and $f$ has derivative $f'(t)$ at $t$ relative to $[t_0, \infty)$.
--
--   The **norming function** of Theorem 7 is
--   $$
--   a(t) = \frac{1 - F(t)}{F'(t)} = \frac{1 - F(t)}{f(t)},
--   $$
--   the reciprocal of the hazard rate; it is positive for $t \ge t_0$ under the density predicate.
--
--   These are the objects in which the finite-$t$ approximation theorems of §4 are stated.
--
--   **Formalization Note** $F$ is Mathlib's `cdf μ` for a measure `μ` on `ℝ` (a probability measure in every theorem). Derivatives are taken within $[t_0, \infty)$, so nothing is assumed about $F$ to the left of $t_0$ (the paper's "for $t \ge t_0$"). `normA μ f t` is defined for every $t$, but is only used at $t \ge t_0$, where $f(t) > 0$; the conditional probability divides by $\mu((t,\infty))$, which is positive for $t \ge t_0$ because $F$ is strictly increasing there.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 792 (PDF 1), (1); pp. 801–802 (PDF 10–11), Theorem 7 (density hypothesis and a(t) = (1 − F(t))/F′(t))

import Mathlib
import Definitions.Def_BalkemaDeHaan_ParetoBounds_ResidualLife

open MeasureTheory ProbabilityTheory

namespace BalkemaDeHaan.FiniteT

/-- "`F = cdf μ` has a positive, differentiable density `F′ = f` for `t ≥ t₀`"
(Theorem 7, pp. 801–802): for every `t ≥ t₀`, `F` has derivative `f t` at `t` within
`[t₀, ∞)`, `f t > 0`, and `f` has derivative `f' t` at `t` within `[t₀, ∞)`. -/
def HasPosDiffDensity (μ : Measure ℝ) (t₀ : ℝ) (f f' : ℝ → ℝ) : Prop :=
  ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t ∧
    HasDerivWithinAt f (f' t) (Set.Ici t₀) t

/-- The norming function of Theorem 7 (p. 802): `a(t) = (1 - F(t)) / F′(t)` with
`F = cdf μ` and `F′ = f`. It is meaningful for `t ≥ t₀`, where `f t > 0`. -/
noncomputable def normA (μ : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 - cdf μ t) / f t

end BalkemaDeHaan.FiniteT


