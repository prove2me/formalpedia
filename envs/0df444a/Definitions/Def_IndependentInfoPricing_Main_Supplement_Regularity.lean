-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity
-- name    : IndependentInfoPricing_Main_Supplement_Regularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:47:04.122693+00:00
-- url     : https://prove2.me/theorems/a3e2dabe-29e6-4ed6-85e4-fa5475afd1e8
-- title:
--   One-dimensional revenue curves, hazard quantities and regular magnitudes
-- statement:
--   This file fixes the one-dimensional notation of §§4.1–4.2 for a law $D$ on $\mathbb R$ (in the applications a nonnegative magnitude $X$, $Y$, $X_i$ or $Y_j$).
--
--   1. The **survival function** is $S_D(t)=\Pr(D\ge t)$ (closed tail), the **revenue curve** is $\rho_D(t)=t\,S_D(t)$, and the **capped revenue** is
--   $$H_D(z)=\sup_{0\le t\le z}\rho_D(t),\qquad z\ge 0 .$$
--   2. The **smallest monopoly price** $p^0_D$ is the least $p\ge 0$ with $\operatorname{Rev}(D)=p\,S_D(p)$, where $\operatorname{Rev}(D)=\sup_{p\ge0}p\,S_D(p)$ is the published `scalarRevenue`.
--   3. **Scope of §§4.2 and 4.4.** $D$ is a probability law with a Lebesgue density $f$ (valued in $[0,\infty]$) whose topological support is an interval; on the interior of the support $f$ is finite, positive and continuously differentiable. A **magnitude in scope** is moreover nonnegative and has a finite monopoly price (the supremum defining $\operatorname{Rev}(D)$ is attained).
--   4. On the interior of the support the **hazard rate** is $h_D=f/S_D$ and the **dimensionless hazard** is $\eta_D(t)=t\,h_D(t)$; at the left endpoint of the support $\eta_D$ is the one-sided limit from the interior (taken as a $\liminf$, possibly $+\infty$), and strictly below the support $\eta_D=0$ because $h_D=0$ there.
--   5. The **virtual value** is $\psi_D(t)=t-1/h_D(t)$, $c_D=-\psi_D$, and the **hazard odds** are $\Lambda_D=\eta_D/(1-\eta_D)$.
--   6. $D$ is **regular** when $\psi_D$ is nondecreasing on the support.
--
--   These objects are shared by Lemmas 4.2–4.6, Theorem 4.1 and Lemmas 4.13–4.18.
--
--   **Formalization Note** The density is a version in $[0,\infty]$ so that `volume.withDensity` applies directly. Regularity is imposed on the interior of the support, where $\psi_D$ is computed pointwise; endpoint values are one-sided limits. `cappedRevenue` is a real `sSup` used only for $z\ge0$ (nonempty set bounded by $z$); `monopolyPrice` is a real `sInf` used only under `FiniteMonopolyPrice`, where the set is nonempty and bounded below by $0$. The value of $\eta_D$ at or beyond a finite right endpoint is a placeholder $0$ that no statement uses.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §4.1 and §4.2.2, printed p.21–23 (PDF p.23–25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Laws

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- Survival function `S_D(t) = Pr(D ≥ t)` (closed tail), as a real number. -/
def survival (D : Measure ℝ) (t : ℝ) : ℝ := (D (Set.Ici t)).toReal

/-- Revenue curve `ρ_D(t) = t · S_D(t)`. -/
def revenueCurve (D : Measure ℝ) (t : ℝ) : ℝ := t * survival D t

/-- Capped revenue `H_D(z) = sup_{0 ≤ t ≤ z} ρ_D(t)`; used only for `z ≥ 0`, where the set is
nonempty and bounded by `z`. -/
def cappedRevenue (D : Measure ℝ) (z : ℝ) : ℝ := sSup (revenueCurve D '' Set.Icc 0 z)

/-- The smallest monopoly price `p⁰_D`; used only under `FiniteMonopolyPrice D`, where the set
of nonnegative maximizers is nonempty. -/
def monopolyPrice (D : Measure ℝ) : ℝ :=
  sInf {p : ℝ | 0 ≤ p ∧ scalarRevenue D = ENNReal.ofReal p * D (Set.Ici p)}

/-- §4.1 scope of a magnitude law: a probability law with Lebesgue density version `f`
(values in `[0,∞]`), whose topological support is an interval; on its
interior `f` is finite, positive and continuously differentiable.  Endpoint values of the hazard
rate are taken as one-sided limits in `eta`, so no condition on `f` at the endpoints is needed. -/
def IntervalDensity (D : Measure ℝ) (f : ℝ → ℝ≥0∞) : Prop :=
  IsProbabilityMeasure D ∧ Measurable f ∧ D = volume.withDensity f ∧
  (lawSupport D).OrdConnected ∧
  (∀ t ∈ interior (lawSupport D), f t ≠ ∞ ∧ 0 < f t) ∧
  ContDiffOn ℝ 1 (fun t => (f t).toReal) (interior (lawSupport D))

/-- Dimensionless hazard `t · f(t) / S(t)` computed pointwise. -/
def pointEta (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal t * f t / D (Set.Ici t)

/-- The dimensionless hazard rate `η_D(t) = t h_D(t)` with §4.1's conventions: on the interior of
the support it is `t f(t)/S(t)`; at the left endpoint of the support it is the one-sided limit from
the interior (here the `liminf`, which is the limit whenever it exists; possibly `∞`); strictly
below the support the hazard rate is `0`.  At and beyond a finite right endpoint the value `0` is
a placeholder that no statement uses (every statement needs `0 < η`, or `t` below the monopoly
price, which lies inside the support). -/
def eta (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if t ∈ interior (lawSupport D) then pointEta D f t
    else if t ∈ lawSupport D ∧ ∀ u ∈ lawSupport D, t ≤ u then
      Filter.liminf (pointEta D f) (𝓝[>] t)
    else 0

/-- Real form of `η_D`, used where `η_D` is finite. -/
def etaReal (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ) : ℝ := (eta D f t).toReal

/-- Virtual value `ψ_D(t) = t − 1/h_D(t) = t − S_D(t)/f(t)`, used on the interior of the
support, where `f(t) > 0`. -/
def virtualValue (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ) : ℝ :=
  t - survival D t / (f t).toReal

/-- `c_D(t) = −ψ_D(t) = 1/h_D(t) − t`. -/
def reverseVirtual (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ) : ℝ := -virtualValue D f t

/-- Hazard odds `Λ_D(t) = η_D(t)/(1 − η_D(t))`, used where `η_D(t) < 1`. -/
def hazardOdds (D : Measure ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ) : ℝ :=
  etaReal D f t / (1 - etaReal D f t)

/-- Regularity (§4.1): the virtual value is nondecreasing on the support.  It is imposed on the
interior of the support, where `ψ_D` is computed from the density; the endpoint values are the
one-sided limits, so monotonicity there follows. -/
def Regular (D : Measure ℝ) (f : ℝ → ℝ≥0∞) : Prop :=
  MonotoneOn (virtualValue D f) (interior (lawSupport D))

/-- A nonnegative magnitude in the scope of §§4.2 and 4.4 with density version `f`:
`D ≥ 0`, positive `C¹` density on an interval support, finite monopoly price. -/
def MagnitudeScope (D : Measure ℝ) (f : ℝ → ℝ≥0∞) : Prop :=
  D (Set.Iio 0) = 0 ∧ IntervalDensity D f ∧ FiniteMonopolyPrice D

/-- A regular magnitude in the scope of §§4.2 and 4.4, for some density version. -/
def RegularMagnitude (D : Measure ℝ) : Prop :=
  ∃ f : ℝ → ℝ≥0∞, MagnitudeScope D f ∧ Regular D f

end IndependentInfoPricing.Main.Supplement


