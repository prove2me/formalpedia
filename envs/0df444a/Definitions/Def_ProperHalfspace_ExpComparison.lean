-- Prove2me | Definitions.Def_ProperHalfspace_ExpComparison
-- name    : ProperHalfspace_ExpComparison
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:48.795274+00:00
-- url     : https://prove2.me/theorems/bb6144ff-835d-4b2e-919f-f1c80d4086e0
-- title:
--   The exponential comparison $D(t,s)$ of Appendix A
-- statement:
--   For $w\in\mathbb R^n$ let $\beta_w=(\sum_iw_i^4)^{1/2}$. For $t\in\mathbb R$ and $z\in\mathbb R^n$,
--   $$\tilde P_t(z)=\prod_i\bigl(\cos(tw_i)+\mathrm iz_i\sin(tw_i)\bigr),\qquad Q_t(z)=e^{\mathrm itw\cdot z},\qquad R_t(z)=\tilde P_t(z)-Q_t(z),$$
--   and $D(t,s)=\mathbf E_{z\sim N(0,I_n)}[R_t(z)\overline{R_s(z)}]$. Here $\tilde P_t$ is the multilinear extension of $x\mapsto e^{\mathrm itw\cdot x}$ and $Q_t$ the direct evaluation of the exponential on a Gaussian input.
--
--   **Formalization Note** $R_t$ is complex valued, and the conjugate is on $R_s$, as on the page.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), App. A, (32), p.39; (33) and the display after it, p.40

import Mathlib
import Definitions.Def_ProperHalfspace_Gaussian

open MeasureTheory

namespace ProperHalfspace

/-!
# The exponential comparison of Appendix A

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), App. A, (32), p.39, and (33), p.40.

**Formalization Note.** `R_t` is complex valued, and `D(t, s)` carries the conjugate on `R_s`, as on the page.
-/

/-- `β_w = (Σᵢ wᵢ⁴)^{1/2}` (p.15, p.39). -/
noncomputable def betaW {n : ℕ} (w : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, w i ^ 4)

/-- `R_t(z) = P̃_t(z) − Q_t(z)`, with `P̃_t(z) = Πᵢ (cos(t wᵢ) + i zᵢ sin(t wᵢ))` and `Q_t(z) = e^{i t w·z}`, (33), p.40. -/
noncomputable def expDiff {n : ℕ} (w : Fin n → ℝ) (t : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (∏ i, ((Real.cos (t * w i) : ℂ) + Complex.I * (z i : ℂ) * (Real.sin (t * w i) : ℂ))) -
    Complex.exp (Complex.I * ((t * ∑ i, w i * z i : ℝ) : ℂ))

/-- `D(t, s) = E_z[R_t(z) \overline{R_s(z)}]` (p.40). -/
noncomputable def expCorr {n : ℕ} (w : Fin n → ℝ) (t s : ℝ) : ℂ :=
  ∫ z, expDiff w t z * (starRingEnd ℂ) (expDiff w s z) ∂stdGauss n

end ProperHalfspace


