-- Prove2me | Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
-- name    : BalkemaDeHaan_DiscreteDomain_ResidualLife
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:06:05.607452+00:00
-- url     : https://prove2.me/theorems/5c4fa347-7b0f-47e0-b3ab-18c20de172c6
-- title:
--   (1) and D_r(G) — the residual life distribution F_t, weak convergence, and the domain of residual life time attraction
-- statement:
--   Let $X$ be a real random variable with law $\mu$, distribution function $F$ and tail $R(x) = 1 - F(x) = P\{X > x\}$.
--
--   1. The **residual life distribution function** at age $t$ is
--   $$F_t(x) = P\{X - t \le x \mid X > t\} = \frac{\mu\big((t, t+x]\big)}{\mu\big((t,\infty)\big)},$$
--   which vanishes for $x < 0$.
--   2. A family $(H_t)_t$ of distribution functions **converges weakly** to $G$ as $t \to \infty$ if $H_t(x) \to G(x)$ at every continuity point $x$ of $G$; nothing is required at the jumps of $G$.
--   3. The **domain of residual life time attraction** $D_r(G)$ consists of all distribution functions $F$ with $F(x) < 1$ for all $x$ for which there exist normalizing functions $a(t) > 0$ and $b(t)$ such that
--   $$F_t\big(b(t) + x\,a(t)\big) \to G(x) \quad \text{weakly as } t \to \infty.$$
--
--   These are the objects in which Theorem 5 and its proof are stated: residual life time attraction asks which laws, viewed from a great age $t$ and suitably rescaled, look like the limit $G$.
--
--   **Formalization Note** The law is a measure $\mu$ on $\mathbb R$ and $R(x)$ is `(μ (Set.Ioi x)).toReal`. The paper observes that $F \in D_r(G)$ implies $F(x) < 1$ for all $x$; since $F_t$ divides by $R(t)$, this condition is built into `InDr` as `∀ x, 0 < μ (Set.Ioi x)`. The normalization $a(t) > 0$ is required for every real $t$, which loses nothing because only large $t$ matter.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 792 (PDF 1), (1); p. 798 (PDF 7), definition of D_r(G)

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife

open MeasureTheory ProbabilityTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- The domain of residual life time attraction `D_r(G)` (p. 798, PDF 7): the law `μ` (with
distribution function `F`) belongs to `D_r(G)` iff `F(x) < 1` for all `x` and there are
normalizing functions `a(t) > 0` and `b(t)` with `F_t(b(t) + x a(t)) → G(x)` weakly as `t → ∞`.
The page notes that `F ∈ D_r(G)` implies `F(x) < 1` for all `x`; it is built into the
definition, since `F_t` is undefined otherwise. -/
def InDr (μ : Measure ℝ) (G : ℝ → ℝ) : Prop :=
  (∀ x, 0 < μ (Set.Ioi x)) ∧
  ∃ a b : ℝ → ℝ, (∀ t, 0 < a t) ∧
    BalkemaDeHaan.LimitTypes.WeakConv (fun t x => BalkemaDeHaan.LimitTypes.residualCDF μ t (b t + x * a t)) G

end BalkemaDeHaan.DiscreteDomain


