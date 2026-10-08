-- Prove2me | Definitions.Def_BoundedNV_ExpFam_Logit
-- name    : BoundedNV_ExpFam_Logit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:28.250902+00:00
-- url     : https://prove2.me/theorems/6d59478c-e355-45a4-9369-11ccb78d9b56
-- title:
--   §3–§4, pp. 571–572 — demand density, expected profit π, decision domain S and the logit choice density ψ
-- statement:
--   This file fixes the newsvendor model under bounded rationality of Su (2008), §3–§4.
--
--   1. **Demand.** Demand $D$ has a density $f$: $f \ge 0$, $f(x) = 0$ for $x < 0$ (demand is nonnegative), $f$ is Lebesgue integrable and $\int_{\mathbb R} f = 1$.
--   2. **Expected sales.** For an order quantity $x\in\mathbb R$,
--   $$E\min(D,x) = \int_{\mathbb R} \min(t,x)\, f(t)\,dt .$$
--   3. **Expected profit** (eq. (3)). With unit price $p$ and unit cost $c$,
--   $$\pi(x) = p\,E\min(D,x) - c\,x .$$
--   4. **Decision domain.** $S$ is the smallest interval containing the support of $f$, taken as the convex hull of the set $\{x : f(x)\ne 0\}$.
--   5. **Logit choice density** (eq. (2)). For a utility $u$ on a domain $S$ and a bounded-rationality parameter $\beta$,
--   $$\psi(y) = \frac{e^{u(y)/\beta}}{\int_S e^{u(v)/\beta}\,dv}\quad (y\in S),\qquad \psi(y) = 0 \quad (y\notin S),$$
--   and for a function $g$ the expectation of $g(Y)$ under the choice $Y$ is $\int_{\mathbb R} g(y)\,\psi(y)\,dy$.
--
--   The **behavioral solution** $X^\flat$ of the newsvendor problem (eq. (4)) is the random order with density $\psi$ for $u = \pi$ and $S$ the decision domain of $f$.
--
--   **Formalization Note** The density, the expectations and $E\min(D,x)$ are Bochner/Lebesgue integrals, which Lean sets to $0$ when the integrand is not integrable; the theorems of this mission assert the integrability they need. The support of $f$ is its pointwise support $\{x : f(x)\neq 0\}$, so $S$ is computed from the given function $f$: two versions of the density that differ on a Lebesgue-null set can have different decision domains. The paper's "smallest interval containing the support" is read for the density as given.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, pp. 571–572 (PDF pp. 6–7), eqs. (2)–(4)

import Mathlib
import Definitions.Def_BoundedNV_Uniform_Logit

namespace BoundedNV.ExpFam

/-- `f` is a demand density: nonnegative, zero on (−∞, 0) (demand is nonnegative), total mass 1. -/
structure IsDemandDensity (f : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ f x
  zero_of_neg : ∀ x, x < 0 → f x = 0
  integrable : MeasureTheory.Integrable f
  integral_eq_one : ∫ x, f x = 1

/-- The decision domain `S`: "the smallest interval containing the support of f" (p. 572). -/
def decisionDomain (f : ℝ → ℝ) : Set ℝ := convexHull ℝ (Function.support f)

end BoundedNV.ExpFam


