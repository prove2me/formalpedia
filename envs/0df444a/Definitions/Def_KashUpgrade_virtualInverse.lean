-- Prove2me | Definitions.Def_KashUpgrade_virtualInverse
-- name    : KashUpgrade_virtualInverse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:13.571038+00:00
-- url     : https://prove2.me/theorems/c561a586-095a-4be0-b47a-d7ee31267ea8
-- title:
--   The extended inverse $v^{-1}$ of the virtual valuation
-- statement:
--   The inverse of the virtual valuation, extended to values too large or too small to be in the image of $v$:
--   $$
--   v^{-1}(\gamma):=\min\bigl(\inf\{\theta\mid v(\theta)\ge\gamma\},\ \zeta\bigr),\qquad \inf\emptyset=+\infty .
--   $$
--
--   **Formalization Note** The value lies in $[0,\infty]$, so $\inf\emptyset=+\infty$ holds as printed. The infimum ranges over the interior $(0,\zeta)$ of the support, where $v$ is defined. This agrees with the paper: the end point $0$ only matters through the infimum, and the end point $\zeta$ is covered by the minimum. Under Assumption 2 the value is finite for every real $\gamma$, and thresholds are its real value.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (9), p.13, and footnote 7

import Mathlib
import Definitions.Def_KashUpgrade_virtualValue

namespace KashUpgrade

/-- **The extended inverse of the virtual valuation.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (9), p.13:
`v⁻¹(γ) := min (inf {θ | v θ ≥ γ}, ζ)`, with `inf ∅ = +∞` (footnote 7).

**Formalization Note** The value is taken in `ℝ≥0∞`, a complete lattice, so `inf ∅ = +∞` holds as
printed and the minimum with `ζ` is the printed one. The infimum ranges over the interior `(0, ζ)`
of the support, where `v` is defined. Under Assumption 2 this agrees with the paper: the end point
`0` only matters through the infimum, the end point `ζ` is covered by the minimum, and outside the
support Lean's `x / 0 = 0` would turn `v` into an artefact. Under Assumption 2 the value is finite
for every real `γ`, because `v θ → ∞` when `ζ = ∞`; thresholds are its `toReal`. -/
noncomputable def virtualInverse (f : ℝ → ℝ) (ζ : ENNReal) (γ : ℝ) : ENNReal :=
  min (⨅ θ ∈ {θ : ℝ | 0 < θ ∧ ENNReal.ofReal θ < ζ ∧ γ ≤ virtualValue f θ}, ENNReal.ofReal θ) ζ

end KashUpgrade


