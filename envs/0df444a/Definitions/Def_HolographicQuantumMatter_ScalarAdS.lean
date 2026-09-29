-- Prove2me | Definitions.Def_HolographicQuantumMatter_ScalarAdS
-- name    : HolographicQuantumMatter_ScalarAdS
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T17:44:01.572385+00:00
-- url     : https://prove2.me/theorems/bc149968-4e72-4a13-bcba-24d2942d527c
-- title:
--   Scalar field in Poincaré AdS$_{d+2}$: radial equation and $\Delta_\pm$
-- statement:
--   Setting of Hartnoll–Lucas–Sachdev §1.6.2. The boundary field theory has $d$ spatial dimensions; the bulk is Poincaré $\mathrm{AdS}_{d+2}$ of radius $L$, $ds^2=L^2(-dt^2+d\vec x_d^2+dr^2)/r^2$, with boundary at $r\to0$. A scalar of mass squared $m^2$ decomposed as $\phi(r)e^{-i\omega t+ik\cdot x}$ obeys the radial equation (27).
--
--   1. **Radial operator.** $\mathcal D_{d,\omega,k,m^2,L}[\phi](r)=\phi''(r)-\frac{d}{r}\phi'(r)+\left(\omega^2-k^2-\frac{m^2L^2}{r^2}\right)\phi(r)$.
--   2. **Radial solution.** $\phi:\mathbb R\to\mathbb R$ is a solution if it is $C^2$ on $(0,\infty)$ and $\mathcal D[\phi](r)=0$ for all $r>0$.
--   3. **Exponents.** $\Delta_\pm=\frac{d+1}{2}\pm\sqrt{\frac{(d+1)^2}{4}+m^2L^2}$, the two roots of $\Delta(\Delta-d-1)=m^2L^2$ (29).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The boundary theory has $d$ spatial dimensions (so the bulk is $\mathrm{AdS}_{d+2}$), following the source's convention. The bulk mass squared is a real parameter $m^2$ (called `msq`), allowed to be negative; the source writes $(mL)^2$ for $m^2L^2$. Fields are real-valued functions of $r$; only their values on $r>0$ matter. The real square root returns $0$ on negative input, so $\Delta_\pm$ are only meaningful at or above the Breitenlohner–Freedman bound; theorems using them carry that hypothesis.
-- source:
--   Hartnoll, Lucas, Sachdev, *Holographic quantum matter*, arXiv:1612.07324v3, https://arxiv.org/abs/1612.07324, Section 1.6.2, p. 9–10, eqs. (23), (25)–(29)

import Mathlib

namespace HolographicQuantumMatter

/-- Left-hand side of the radial wave equation (27) of Hartnoll–Lucas–Sachdev,
`φ'' - (d/r) φ' + (ω² - k² - m²L²/r²) φ`, for a scalar of mass squared `msq`
in Poincaré `AdS_{d+2}` of radius `L`. -/
noncomputable def radialOperator (d : ℕ) (ω k msq L : ℝ) (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv φ) r - ((d : ℝ) / r) * deriv φ r
    + (ω ^ 2 - k ^ 2 - msq * L ^ 2 / r ^ 2) * φ r

/-- `φ` is a classical (`C²`) solution of the radial equation (27) on `r > 0`. -/
def IsRadialSolution (d : ℕ) (ω k msq L : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ (Set.Ioi 0) ∧ ∀ r : ℝ, 0 < r → radialOperator d ω k msq L φ r = 0

/-- The larger root `Δ₊ = (d+1)/2 + √((d+1)²/4 + m²L²)` of equation (29). -/
noncomputable def deltaPlus (d : ℕ) (msq L : ℝ) : ℝ :=
  ((d : ℝ) + 1) / 2 + Real.sqrt (((d : ℝ) + 1) ^ 2 / 4 + msq * L ^ 2)

/-- The smaller root `Δ₋ = (d+1)/2 - √((d+1)²/4 + m²L²)` of equation (29). -/
noncomputable def deltaMinus (d : ℕ) (msq L : ℝ) : ℝ :=
  ((d : ℝ) + 1) / 2 - Real.sqrt (((d : ℝ) + 1) ^ 2 / 4 + msq * L ^ 2)

end HolographicQuantumMatter


