-- Prove2me | Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife
-- name    : BalkemaDeHaan_LimitTypes_ResidualLife
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:33.712786+00:00
-- url     : https://prove2.me/theorems/b5a5d126-fd6f-4b25-a586-4ec0c62a0561
-- title:
--   (1)–(2) — the distribution tail R, the residual life d.f. F_t, the normed tail of (2), weak convergence and types
-- statement:
--   Let $X$ be a real random variable with law $\mu$, distribution function $F$ and **distribution tail**
--   $$R(x) = 1 - F(x) = P\{X > x\} = \mu\big((x,\infty)\big).$$
--   The same notation is used for any law $\nu$ on $\mathbb R$: its tail is $x \mapsto \nu((x,\infty))$.
--
--   1. The **residual life distribution function** at age $t$ is, as in (1),
--   $$F_t(x) = P\{X - t \le x \mid X > t\} = \frac{\mu\big((t, t+x]\big)}{\mu\big((t,\infty)\big)},$$
--   which vanishes for $x < 0$. It is meaningful when $R(t) > 0$.
--   2. Given functions $a(t) > 0$ and $b(t)$, the **normed conditional tail** of (2) is
--   $$P\Big(\frac{X - b(t)}{a(t)} > x \;\Big|\; X > t\Big) = \frac{\mu\big((t,\infty) \cap (b(t) + x a(t), \infty)\big)}{\mu\big((t,\infty)\big)} = \min\Big(1, \frac{R(b(t) + x a(t))}{R(t)}\Big),$$
--   the last form being (3).
--   3. A family $H_t$ of distribution functions (or of distribution tails) **converges weakly** to $G$ as $t \to \infty$ if $H_t(x) \to G(x)$ at every continuity point $x$ of $G$; nothing is asked at the discontinuity points of $G$.
--   4. A function $G$ is **of type** $K$ if $G(x) = K(ax + b)$ for all $x$, for some $a > 0$ and $b \in \mathbb R$.
--
--   These are the objects in which the classification of residual-life limit laws is stated: Theorem 1 normalizes $X - t$ through $F_t(b(t) + x a(t))$, while (2), (3) and Lemma 1 (p. 794) normalize $X$ itself. The two conventions differ by $b(t) \mapsto b(t) + t$.
--
--   **Formalization Note** Only the law of $X$ matters, so $X$ is represented by a measure $\mu$ on $\mathbb R$; probabilities are real numbers via `ENNReal.toReal`. The quotients are Lean divisions, which return $0$ when $R(t) = 0$; every statement using them assumes $R(x) > 0$ for all $x$, as the paper does throughout (p. 792 and §1, p. 793). Weak convergence is along $t \to \infty$ in $\mathbb R$ and is required exactly at the continuity points of the limit.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 792 (PDF 1), (1); pp. 793–794 (PDF 2–3), (2), (3)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.LimitTypes

/-- The distribution tail `R(x) = P{X > x} = μ((x, ∞))` of a law `μ` on `ℝ`
(Balkema, de Haan, *Residual Life Time at Great Age*, Ann. Probab. 2 (1974), p. 792, PDF 1).
For a probability measure `μ` this is `1 - cdf μ x`. -/
noncomputable def tail (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (μ (Set.Ioi x)).toReal

/-- The residual life distribution function of (1), p. 792 (PDF 1):
`F_t(x) = P{X - t ≤ x | X > t} = μ((t, t + x]) / μ((t, ∞))`.
It is `0` for `x < 0` (empty interval). It is meaningful when `μ((t, ∞)) > 0`, which the paper
assumes for every `t` ("`R(x)` is positive for all `x`"); every statement using it carries that
hypothesis. -/
noncomputable def residualCDF (μ : Measure ℝ) (t x : ℝ) : ℝ :=
  (μ (Set.Ioc t (t + x))).toReal / (μ (Set.Ioi t)).toReal

/-- The normed conditional tail of (2), p. 794 (PDF 3):
`P((X - b(t))/a(t) > x | X > t) = μ((t, ∞) ∩ (b(t) + x a(t), ∞)) / μ((t, ∞))`, for `a(t) > 0`.
It equals `min(1, R(b(t) + x a(t)) / R(t))`, the form (3). -/
noncomputable def normedTail (μ : Measure ℝ) (a b : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (μ (Set.Ioi t ∩ Set.Ioi (b t + x * a t))).toReal / (μ (Set.Ioi t)).toReal

/-- Weak convergence, as `t → ∞`, of a family `H t` of distribution functions (or of distribution
tails) to a limit `G`: `H t x → G x` at every continuity point `x` of `G`, and nothing is required
at the discontinuity points of `G`. -/
def WeakConv (H : ℝ → ℝ → ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ x, ContinuousAt G x → Tendsto (fun t => H t x) atTop (𝓝 (G x))

/-- `G` is of type `K`: `G(x) = K(a x + b)` for all `x`, for some `a > 0` and real `b`. -/
def IsOfType (G K : ℝ → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ x, G x = K (a * x + b)

end BalkemaDeHaan.LimitTypes


