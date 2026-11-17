-- Prove2me | Definitions.Def_BilatMatch_Supplement_betaAlpha
-- name    : BilatMatch_Supplement_betaAlpha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:27:12.072344+00:00
-- url     : https://prove2.me/theorems/28d282b5-cced-4a6c-991d-1c4ec9af4177
-- title:
--   The MHR constants $M_t(\xi)$, $\xi_t$, $\beta_\alpha$ and $\gamma_{\mathrm{MHR}}$
-- statement:
--   For $t\in(0,1)$ and $\xi\in\mathbb R$ let
--   $$M_t(\xi)=t\int_0^1\lambda^{t-1}e^{\xi\lambda}\,d\lambda .$$
--   Let $\xi_t$ be the root in $(1-t,2(1-t))$ of the balance equation
--   $$(\xi_t+2t-1)M_t(\xi_t)=t\,e^{\xi_t}\qquad(10)$$
--   (chosen among the roots; that there is exactly one is part of Theorem 4.1). Set $\beta_0=1$ and, for $\alpha>0$ with $t=(1+\alpha)^{-1}$, $\beta_\alpha=M_t(\xi_t)^{-1}$. Finally
--   $$\gamma_{\mathrm{MHR}}=\inf_{0<t<1}\frac1{M_t(\xi_t)}$$
--   (that the infimum is a minimum, numerically $\approx0.72490721$, is part of Theorem 4.1).
--
--   $\beta_\alpha$ is the sharp fixed-multiplier factor and $\gamma_{\mathrm{MHR}}$ the sharp second-best factor for MHR buyers.
--
--   **Formalization Note** $\xi_t$ is selected by `Classical.epsilon` among the roots in the interval; $\gamma_{\mathrm{MHR}}$ is a real `sInf`, whose attainment is asserted in Theorem 4.1.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490adbe231952acc5fc467ea7dfe37f237d7ce95248cd45c10451aedf4984), §4, p.17 (pdf p.19), definitions of M_t, ξ_t, β_α, eqs. (10)–(11)

import Mathlib

open MeasureTheory

namespace BilatMatch.Supplement

/-!
# The MHR constants `M_t`, `ξ_t`, `β_α`, `γ_MHR`

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §4, p.17 (pdf p.19), eqs. (10)–(11).

**Formalization Note**
* `Mt t ξ = t ∫_0^1 λ^{t−1} e^{ξλ} dλ` as an interval integral (`Real.rpow`); for `t ∈ (0, 1)` the
  integrand is integrable on `(0, 1)`, so the integral is the paper's value.
* `xi t` is chosen (`Classical.epsilon`) among the roots of the balance equation (10) in
  `(1 − t, 2(1 − t))`; that such a root exists and is unique is a conjunct of Theorem 4.1, as the paper
  asserts it in the definition.
* `betaAlpha α` is `1` at `α = 0` and `Mt t (xi t)⁻¹` with `t = (1 + α)⁻¹` for `α > 0`; it is used only
  for `α ≥ 0`.
* `gammaMHR` is the infimum of `1/Mt t (xi t)` over `t ∈ (0, 1)`; that it is a minimum (attained) is a
  conjunct of Theorem 4.1.
-/

/-- `M_t(ξ) = t ∫_0^1 λ^{t−1} e^{ξλ} dλ` (p.17). -/
noncomputable def Mt (t ξ : ℝ) : ℝ := t * ∫ l in (0 : ℝ)..1, l ^ (t - 1) * Real.exp (ξ * l)

/-- The balance equation (10): `(ξ + 2t − 1) M_t(ξ) = t e^ξ`. -/
def IsBalanceRoot (t ξ : ℝ) : Prop :=
  ξ ∈ Set.Ioo (1 - t) (2 * (1 - t)) ∧ (ξ + 2 * t - 1) * Mt t ξ = t * Real.exp ξ

/-- `ξ_t`: the root of (10) in `(1 − t, 2(1 − t))` (p.17). -/
noncomputable def xi (t : ℝ) : ℝ := Classical.epsilon (IsBalanceRoot t)

/-- `β_0 = 1`, `β_α = M_t(ξ_t)⁻¹` with `t = (1 + α)⁻¹` for `α > 0` (p.17). -/
noncomputable def betaAlpha (α : ℝ) : ℝ :=
  if α = 0 then 1 else (Mt (1 + α)⁻¹ (xi (1 + α)⁻¹))⁻¹

/-- `γ_MHR = min_{0<t<1} 1/M_t(ξ_t)` (eq. (11), p.17), as an infimum. -/
noncomputable def gammaMHR : ℝ := sInf ((fun t => (Mt t (xi t))⁻¹) '' Set.Ioo 0 1)

end BilatMatch.Supplement


