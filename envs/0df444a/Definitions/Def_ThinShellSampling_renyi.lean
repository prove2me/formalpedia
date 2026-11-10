-- Prove2me | Definitions.Def_ThinShellSampling_renyi
-- name    : ThinShellSampling_renyi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:26.50735+00:00
-- url     : https://prove2.me/theorems/9c977cc1-2ce5-4682-8277-e3c0795c4af5
-- title:
--   Rényi divergence $\mathsf R_q(\mu\,\|\,\nu)$ and $\mathsf R_\infty$
-- statement:
--   Let $\mu,\nu$ be probability measures on a measurable space with $\mu\ll\nu$. For an order $q>1$ the **Rényi divergence** of $\mu$ from $\nu$ is
--
--   $$
--   \mathsf R_q(\mu\,\|\,\nu)=\frac{1}{q-1}\log\int\Big(\frac{d\mu}{d\nu}\Big)^q\,d\nu=\frac{1}{q-1}\log\Big\|\frac{d\mu}{d\nu}\Big\|^q_{L^q(\nu)}\in[0,\infty],
--   $$
--
--   and at $q=1$ it is the Kullback–Leibler divergence $\mathrm{KL}(\mu\,\|\,\nu)=\lim_{q\downarrow1}\mathsf R_q(\mu\,\|\,\nu)$. The **Rényi-infinity divergence** is $\mathsf R_\infty(\mu\,\|\,\nu)=\log\operatorname{ess\,sup}_\nu \frac{d\mu}{d\nu}$. When $\mu\not\ll\nu$ all these divergences equal $+\infty$.
--
--   Rényi divergences measure the warmness of a sampler's law: an $\mathsf R_q$-warm start is the input, and an $\mathsf R_q$ bound the output guarantee, of every sampler in this mission.
--
--   **Formalization Note** Values lie in $[0,\infty]$. The value is $\infty$ whenever $\mu\not\ll\nu$ or either measure is not a probability measure (for instance the zero measure produced by a non-measurable push-forward), so an upper bound on the divergence of a junk law is false rather than vacuous. At $q=1$ Mathlib's `klDiv` is used. Only orders $q\ge1$ are used.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.3, eq. (1.2), p.13 (PDF p.15); footnote 1, p.1 (PDF p.3); R_∞ on p.13

import Mathlib

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- **Rényi divergence** `R_q(μ ‖ ν)` of order `q ≥ 1`, valued in `[0, ∞]`.

Y. Kook, S. S. Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave
Sampling with Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256
25a041a9…), §1.3, eq. (1.2), p.13 (PDF p.15): for `q > 1`,
`R_q(μ ‖ ν) = (q − 1)⁻¹ log ‖dμ/dν‖^q_{L^q(ν)}`; footnote 1, p.1 (PDF p.3): `KL = lim_{q↓1} R_q`.

**Formalization Note.**
* When `μ` and `ν` are probability measures with `μ ≪ ν` and `q ≠ 1`, the value is
  `ENNReal.ofReal (log I / (q − 1))` with `I = ∫ (dμ/dν)^q dν`, and `∞` when `I = ∞`. For `q > 1`
  and probability measures `I ≥ 1` (Jensen), so the clamp `ofReal` never cuts a negative value.
* At `q = 1` the value is Mathlib's Kullback–Leibler divergence `InformationTheory.klDiv μ ν`.
* In every other case (`μ` not absolutely continuous w.r.t. `ν`, or either measure not a
  probability measure, e.g. the zero measure produced by a non-measurable push-forward) the value
  is `∞`. This is the paper's convention off absolute continuity, and it makes every upper bound
  on `R_q` of a junk law false rather than vacuous.
* Only orders `q ≥ 1` are used in this development. -/
noncomputable def renyi {α : Type*} [MeasurableSpace α] (q : ℝ) (μ ν : Measure α) : ℝ≥0∞ := by
  classical
  exact
    if IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧ μ ≪ ν then
      (if q = 1 then InformationTheory.klDiv μ ν
       else
        if (∫⁻ x, (μ.rnDeriv ν x) ^ q ∂ν) = ⊤ then ⊤
        else ENNReal.ofReal (Real.log (∫⁻ x, (μ.rnDeriv ν x) ^ q ∂ν).toReal / (q - 1)))
    else ⊤

/-- **Rényi-infinity divergence** `R_∞(μ ‖ ν) = log ess sup_ν dμ/dν`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.3, p.13 (PDF p.15):
"The Rényi-infinity divergence is defined as `R_∞(μ ‖ ν) := log ess sup_ν dμ/dν`."

**Formalization Note.** For probability measures with `μ ≪ ν` the essential supremum is at least
`1`, so the logarithm is nonnegative; it is `∞` when the essential supremum is `∞`. In every
other case (no absolute continuity, or not probability measures) the value is `∞`. -/
noncomputable def renyiInf {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ := by
  classical
  exact
    if IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧ μ ≪ ν then
      (if essSup (μ.rnDeriv ν) ν = ⊤ then ⊤
       else ENNReal.ofReal (Real.log (essSup (μ.rnDeriv ν) ν).toReal))
    else ⊤

end ThinShellSampling


