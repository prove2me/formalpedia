-- Prove2me | Definitions.Def_CachonPushPull_Pareto_Model
-- name    : CachonPushPull_Pareto_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T19:21:58.839013+00:00
-- url     : https://prove2.me/theorems/0df60731-1016-4ada-9cfb-bffe34dd671f
-- title:
--   Cachon (2004) demand model: IGFR demand, expected sales $S(q)$, chain profit $\Pi(q)$, $j(q)$ and hazard rate $h(q)$
-- statement:
--   This file fixes the demand model of Cachon's single-season supplier–retailer model and the basic quantities built from it.
--
--   **Demand.** Demand is a random variable with law $\mu$, a probability measure on $\mathbb R$, and distribution function $F(x) = \mu((-\infty, x])$. The standing assumptions of the paper (§3) are collected in the predicate $\mathrm{DemandModel}(\mu, f)$:
--
--   1. $F(0) = 0$ (there is always some demand);
--   2. $F$ is strictly increasing on $[0, \infty)$;
--   3. $f$ is the density: $F'(x) = f(x)$ for every $x > 0$;
--   4. increasing generalized failure rate (IGFR): the generalized failure rate $g(x) = x h(x) = \dfrac{x f(x)}{1 - F(x)}$ satisfies $g'(x) > 0$ for every $x > 0$.
--
--   **Derived quantities.** For a quantity $q$, with retail price $p$, production cost $c$ and salvage value $v$,
--   $$
--   S(q) = q - \int_0^q F(x)\,dx, \qquad \Pi(q) = (p - v) S(q) - (c - v) q,
--   $$
--   $$
--   j(q) = \frac{S(q)}{1 - F(q)}, \qquad h(q) = \frac{f(q)}{1 - F(q)}.
--   $$
--   $S(q)$ is expected sales when $q$ units are available, $\Pi(q)$ is the integrated supply chain's expected profit, $h$ is the failure (hazard) rate.
--
--   These are the primitives of every statement in the mission.
--
--   **Formalization Note** $F$ is Mathlib's `ProbabilityTheory.cdf μ`, which is monotone, right-continuous, with limits $0$ and $1$; the probability-measure instance is a hypothesis of every theorem, not a field of the structure. The paper assumes $F$ differentiable; here differentiability is required only on $(0, \infty)$, because the exponential law, which the paper lists as IGFR, has a kink at $0$. A positive derivative of $g$ at $x$ forces $g$ to be differentiable there, so no separate differentiability hypothesis on $f$ is stated. $1 - F(q) > 0$ for every $q$ under these assumptions, so the divisions in $j$ and $h$ never hit Lean's convention $x/0 = 0$.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, pp. 225-227, Section 3 (demand assumptions), Eq. (1), Eq. (4), Lemma 1 (h)

import Mathlib

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- The standing demand assumptions of Cachon (2004), §3, p. 225, for a demand law `μ` on `ℝ`
with distribution function `F = cdf μ` and a density `f`:
* `F(0) = 0` (there is always some demand);
* `F` is strictly increasing on `[0, ∞)`;
* `f` is the derivative of `F` at every `x > 0`;
* IGFR: the generalized failure rate `g(x) = x f(x) / (1 - F(x))` has `g'(x) > 0` for `x > 0`
  (a positive derivative forces `g` to be differentiable there).
Differentiability is required on `(0, ∞)` only, so the exponential law (kink at `0`), which the
paper names as IGFR, is admitted. -/
structure DemandModel (μ : Measure ℝ) (f : ℝ → ℝ) : Prop where
  cdf_zero : cdf μ 0 = 0
  strictMonoOn : StrictMonoOn (cdf μ) (Set.Ici 0)
  hasDerivAt : ∀ x : ℝ, 0 < x → HasDerivAt (cdf μ) (f x) x
  igfr : ∀ x : ℝ, 0 < x → 0 < deriv (fun y : ℝ => y * f y / (1 - cdf μ y)) x

/-- Expected sales `S(q) = q - ∫₀^q F(x) dx` (Eq. (1)). -/
noncomputable def S (μ : Measure ℝ) (q : ℝ) : ℝ :=
  q - ∫ x in (0 : ℝ)..q, cdf μ x

/-- The integrated supply chain's expected profit `Π(q) = (p - v) S(q) - (c - v) q` (Eq. (1)). -/
noncomputable def chainProfit (μ : Measure ℝ) (p c v q : ℝ) : ℝ :=
  (p - v) * S μ q - (c - v) * q

/-- `j(q) = S(q) / (1 - F(q))` (Eq. (4)). -/
noncomputable def j (μ : Measure ℝ) (q : ℝ) : ℝ :=
  S μ q / (1 - cdf μ q)

/-- The failure (hazard) rate `h(q) = f(q) / (1 - F(q))`. -/
noncomputable def hazard (μ : Measure ℝ) (f : ℝ → ℝ) (q : ℝ) : ℝ :=
  f q / (1 - cdf μ q)

end CachonPushPull.Pareto


