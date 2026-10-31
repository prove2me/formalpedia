-- Prove2me | Definitions.Def_KashUpgrade_IsTypeDensity
-- name    : KashUpgrade_IsTypeDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:59.809997+00:00
-- url     : https://prove2.me/theorems/5b85c36a-13ab-4f19-ac00-bf7e3e9f8864
-- title:
--   Customer types: a differentiable density on $[0,\zeta]$
-- statement:
--   A function $f$ is a density of the customer type with support $[0,\zeta]$ (or $[0,\zeta)$ if $\zeta=\infty$) if:
--
--   1. $\zeta>0$;
--   2. $f$ is measurable, nonnegative and integrable, and $\int f=1$;
--   3. $f=0$ outside the support and $f>0$ on $(0,\zeta)$;
--   4. $f$ is differentiable on $(0,\zeta)$.
--
--   This is the part of the type law that does not involve the hazard rate.
--
--   **Formalization Note** Differentiability is required on the interior only, because the paper's uniform example has a density that jumps at the end points of its support. Positivity on $(0,\zeta)$ follows from the paper's Assumption 2 (if $f(p)=0$ at an interior $p$, the ratio is $+\infty$ there and monotone decrease forces $f=0$ on $[0,p]$).
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), §3, p.9; Assumption 2, p.13

import Mathlib
import Definitions.Def_KashUpgrade_typeSupport
import Definitions.Def_KashUpgrade_typeInterior

namespace KashUpgrade

/-- **The type law.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), §3, p.9 and Assumption 2, p.13: `f` is a differentiable probability density
of the customer type `θ ≥ 0` whose support is `[0, ζ]` (or `[0, ζ)` if `ζ = ∞`).

**Formalization Note** "Support" is `f = 0` outside the interval and `f > 0` on `(0, ζ)`, which the
paper's Assumption 2 implies. "Differentiable" is meant on the interior: the paper's own uniform example
has a density that jumps at the end points of its support. -/
structure IsTypeDensity (f : ℝ → ℝ) (ζ : ENNReal) : Prop where
  /-- The support has positive length. -/
  zeta_pos : 0 < ζ
  /-- `f` is measurable. -/
  measurable : Measurable f
  /-- `f` is nonnegative. -/
  nonneg : ∀ θ, 0 ≤ f θ
  /-- `f` is integrable. -/
  integrable : MeasureTheory.Integrable f MeasureTheory.volume
  /-- `f` integrates to one. -/
  integral_eq_one : ∫ θ, f θ = 1
  /-- `f` vanishes outside the support. -/
  eq_zero_of_notMem : ∀ θ, θ ∉ typeSupport ζ → f θ = 0
  /-- `f` is positive on `(0, ζ)`. -/
  pos_of_mem : ∀ θ ∈ typeInterior ζ, 0 < f θ
  /-- `f` is differentiable on `(0, ζ)`. -/
  differentiableOn : DifferentiableOn ℝ f (typeInterior ζ)

end KashUpgrade


