-- Prove2me | Definitions.Def_ForwardRM_Cutoffs_Model
-- name    : ForwardRM_Cutoffs_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:56:24.956404+00:00
-- url     : https://prove2.me/theorems/f31bd6fc-e9c9-4e4a-9349-161b6b5ca10e
-- title:
--   §2, §2.1 — the model: K units, periods 1..T, entrants N_t, i.i.d. values with density f on [v̲, v̄], discount δ, marginal revenue m
-- statement:
--   This file fixes the primitives of Board and Skrzypacz's model of revenue management with forward-looking buyers, together with the standing assumptions of §2 and §2.1 of the paper.
--
--   A seller has units of a good to sell over discrete periods $t\in\{1,\dots,T\}$, $T\ge 1$; unsold units are worth zero after period $T$. Payoffs are discounted by a factor $\delta\in(0,1)$. At the start of period $t$ a random number $N_t$ of buyers enters; the law of $N_t$ is a probability mass function on $\{0,1,2,\dots\}$ that may change with $t$, and the $N_t$ are independent across periods. Each buyer wants one unit and has a private value drawn independently from a distribution with continuous density $f$ on the support $[\underline v,\bar v]$, $\underline v<\bar v$; we require $f>0$ on $[\underline v,\bar v]$, $f=0$ outside, and $\int f=1$. The distribution function is $F(v)=\int_{-\infty}^v f$, and the **marginal revenue** (virtual value) of a buyer with value $v$ is
--
--   $$
--   m(v)=v-\frac{1-F(v)}{f(v)} .
--   $$
--
--   As in §2.1, $m$ is assumed strictly increasing and continuously differentiable on $[\underline v,\bar v]$, with $m(\underline v)<0$. In addition $m(\bar v)>0$ (equivalently $\bar v>0$, since $F(\bar v)=1$).
--
--   These data are everything the seller's optimal allocation problem (2.5) depends on: by the mechanism-design reduction of §2.1 the seller maximizes the expected discounted sum of the marginal revenues of the buyers she serves.
--
--   **Formalization Note** The positivity $m(\bar v)>0$ is not stated on the page; it is the hypothesis that footnote 12 (p. 16) uses when it writes $(1-\delta)m(\bar v)>0$, and without it the seller never sells and the cutoff of Theorem 1 does not exist. Positivity of $f$ on the closed support is what makes $m$ defined at every point of $[\underline v,\bar v]$, as the paper's assumptions on $m$ (including $m(\underline v)<0$) require. Independence of the $N_t$ across periods is not modelled as a joint process: the seller's dynamic program only takes expectations over one period's entrants at a time, so only the marginal laws `arrivals t` enter. The value law is the measure with density $f$; $F$ is computed as a lower Lebesgue integral.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, pp. 6–9, §2 (Basics, Entrants, Preferences) and §2.1 (marginal revenue below eq. (2.5)); p. 16, footnote 12

import Mathlib

namespace ForwardRM.Cutoffs

open MeasureTheory

/-- The distribution function of the value density `f`:
`cdfOf f v = ∫_{(-∞, v]} f`, computed as a lower Lebesgue integral of `max (f u) 0`
(finite whenever `∫ f = 1`, as in a `Model`). -/
noncomputable def cdfOf (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  (∫⁻ u in Set.Iic v, ENNReal.ofReal (f u)).toReal

/-- The marginal revenue (virtual value) of a buyer with value `v`
(Board–Skrzypacz, §2.1, p. 9): `m(v) = v - (1 - F(v)) / f(v)`. -/
noncomputable def marginalRevenueOf (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  v - (1 - cdfOf f v) / f v

/-- The primitives of the Board–Skrzypacz model (§2, pp. 6–8, and §2.1, p. 9) together with the
standing assumptions of the paper.

* `T` is the last period; periods are `t ∈ {1, …, T}`.
* `δ ∈ (0, 1)` is the discount factor.
* Buyer values are i.i.d. with continuous density `f` supported on `[vlo, vhi]`
  (`vlo = v̲`, `vhi = v̄`); the density is positive on the support, so that the marginal
  revenue `m(v) = v − (1 − F(v))/f(v)` is defined on all of `[v̲, v̄]`.
* `arrivals t` is the law of the number `N_t` of buyers who enter at the start of period `t`.
  The `N_t` are independent across periods; since the seller's dynamic program only ever takes
  expectations over one period's entrants at a time, only these marginal laws enter.
* §2.1 assumptions on `m`: strictly increasing and continuously differentiable on `[v̲, v̄]`,
  with `m(v̲) < 0`.
* `m(v̄) > 0`: not stated on the page, but used in footnote 12 (p. 16, "`ΔΠ(v̄) = (1−δ)m(v̄) > 0`");
  without it no unit is ever sold and Theorem 1's cutoff does not exist. Since `F(v̄) = 1`,
  it is equivalent to `v̄ > 0`. -/
structure Model where
  /-- The last period `T ≥ 1`. -/
  T : ℕ
  one_le_T : 1 ≤ T
  /-- The discount factor `δ`. -/
  δ : ℝ
  δ_pos : 0 < δ
  δ_lt_one : δ < 1
  /-- Lower end `v̲` of the support of buyer values. -/
  vlo : ℝ
  /-- Upper end `v̄` of the support of buyer values. -/
  vhi : ℝ
  vlo_lt_vhi : vlo < vhi
  /-- The density `f` of buyer values. -/
  f : ℝ → ℝ
  f_continuousOn : ContinuousOn f (Set.Icc vlo vhi)
  f_pos : ∀ v ∈ Set.Icc vlo vhi, 0 < f v
  f_eq_zero : ∀ v, v ∉ Set.Icc vlo vhi → f v = 0
  f_total : ∫⁻ v, ENNReal.ofReal (f v) = 1
  /-- `arrivals t` is the law of the number `N_t` of entrants in period `t`. -/
  arrivals : ℕ → PMF ℕ
  m_strictMonoOn : StrictMonoOn (marginalRevenueOf f) (Set.Icc vlo vhi)
  m_contDiffOn : ContDiffOn ℝ 1 (marginalRevenueOf f) (Set.Icc vlo vhi)
  m_vlo_neg : marginalRevenueOf f vlo < 0
  m_vhi_pos : 0 < marginalRevenueOf f vhi

namespace Model

variable (M : Model)

/-- The law `μ` of a buyer's value: the measure with density `f`. -/
noncomputable def law : Measure ℝ :=
  volume.withDensity (fun v => ENNReal.ofReal (M.f v))

instance law_isProbabilityMeasure : IsProbabilityMeasure M.law :=
  ⟨by rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact M.f_total⟩

/-- The distribution function `F` of buyer values. -/
noncomputable def F (v : ℝ) : ℝ := cdfOf M.f v

/-- The marginal revenue `m(v) = v − (1 − F(v))/f(v)` (§2.1, p. 9). -/
noncomputable def m (v : ℝ) : ℝ := marginalRevenueOf M.f v

end Model

end ForwardRM.Cutoffs


