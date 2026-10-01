-- Prove2me | Definitions.Def_SMHiggsPotential_Defs
-- name    : SMHiggsPotential_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T23:36:50.082199+00:00
-- url     : https://prove2.me/theorems/dcf845ea-712c-44d8-9de0-c971a4efe7ab
-- title:
--   Standard Model Lagrangian, box 2: the scalar-potential terms, the Higgs doublet and $v=2M/g$
-- statement:
--   **Parameters.** The $SU(2)$ coupling $g$, the $W$ mass $M$, the Higgs mass $m_h$ and the tadpole coefficient $\beta_h$ (all real). Derived constants, in Veltman's conventions:
--   $$\alpha_h=\frac{m_h^2}{4M^2},\qquad v=\frac{2M}{g},\qquad \lambda=\frac{g^2\alpha_h}{2}=\frac{g^2m_h^2}{8M^2}.$$
--
--   **Fields** at one spacetime point: real $H$ and $\phi^0$, and complex $\phi^+$ with $\phi^-=\overline{\phi^+}$, so $\phi^+\phi^-=|\phi^+|^2$.
--
--   **The scalar terms of box 2.** `scalarLagrangian` is the sum of the purely scalar, non-derivative terms of box 2 of the chart. It **excludes** the Goldstone mass terms $-M^2\phi^+\phi^-$ and $-\frac{M^2}{2c_w^2}\phi^0\phi^0$, which come from gauge fixing:
--   $$\mathcal L_V=-\tfrac12 m_h^2H^2-\beta_h\Big[\tfrac{2M^2}{g^2}+\tfrac{2M}{g}H+\tfrac12(H^2+\phi^0\phi^0+2\phi^+\phi^-)\Big]+\tfrac{2M^4}{g^2}\alpha_h-gM\alpha_h\big[H^3+H\phi^0\phi^0+2H\phi^+\phi^-\big]$$
--   $$-\tfrac18g^2\alpha_h\big[H^4+(\phi^0)^4+4(\phi^+\phi^-)^2+4(\phi^0)^2\phi^+\phi^-+4H^2\phi^+\phi^-+2(\phi^0)^2H^2\big].$$
--
--   **Higgs doublet.** $\Phi=\big(\phi^+,\ (v+H+i\phi^0)/\sqrt2\big)\in\mathbb C^2$, with Hermitian square norm $\Phi^\dagger\Phi=|\Phi_1|^2+|\Phi_2|^2$ (`doubletNormSq`).
--
--   *How the print is read:* the chart prints the cubic coefficient as $g\alpha$. Here it is read as $gM\alpha_h$. This is the only value for which the scalar terms combine into a potential of the doublet. Division by zero returns $0$ in Lean, so $\alpha_h$ and $v$ are only meaningful when $M\neq0$ and $g\neq0$.
-- source:
--   Standard Model Lagrangian in Veltman's conventions (Feynman-'t Hooft gauge), as printed in the five-box chart supplied by the proposer (after M. Veltman, *Diagrammatica: The Path to Feynman Diagrams*, Cambridge University Press, 1994). Box 2, the non-derivative scalar terms: $-\frac12 m_h^2H^2$, the $\beta_h[\dots]$ term, $+\frac{2M^4}{g^2}\alpha_h$, $-g\alpha[H^3+H\phi^0\phi^0+2H\phi^+\phi^-]$ and $-\frac18g^2\alpha_h[H^4+\dots]$.

import Mathlib

/-!
# Standard Model Lagrangian (Veltman form), sector 2: the Higgs potential terms
-/

namespace SMHiggsPotential

open Complex

/-- Veltman's Higgs self-coupling parameter `α_h = m_h² / (4 M²)`. -/
noncomputable def alphaH (M mh : ℝ) : ℝ := mh ^ 2 / (4 * M ^ 2)

/-- The Higgs vacuum expectation value `v = 2 M / g`. -/
noncomputable def vev (g M : ℝ) : ℝ := 2 * M / g

/-- The quartic coupling `λ = g² α_h / 2 = g² m_h² / (8 M²)` of the doublet potential. -/
noncomputable def quarticCoupling (g M mh : ℝ) : ℝ := g ^ 2 * alphaH M mh / 2

/-- The non-derivative, purely scalar terms of sector 2 of the printed Lagrangian, excluding
the gauge-fixing Goldstone mass terms `-M² φ⁺φ⁻` and `-(M²/2c_w²) φ⁰φ⁰`:
```
-½ m_h² H² - β_h [2M²/g² + (2M/g) H + ½(H² + φ⁰φ⁰ + 2φ⁺φ⁻)] + (2M⁴/g²) α_h
  - g M α_h [H³ + H φ⁰φ⁰ + 2 H φ⁺φ⁻]
  - ⅛ g² α_h [H⁴ + (φ⁰)⁴ + 4(φ⁺φ⁻)² + 4(φ⁰)²φ⁺φ⁻ + 4H²φ⁺φ⁻ + 2(φ⁰)²H²]
```
The coefficient printed as `g α` in the cubic term is read as `g M α_h`.
`H, φ⁰` are real, `φ⁺ = φp` is complex and `φ⁻ = conj φ⁺`, so `φ⁺φ⁻ = |φp|²`. -/
noncomputable def scalarLagrangian (g M mh βh H φ0 : ℝ) (φp : ℂ) : ℝ :=
  - (1 / 2) * mh ^ 2 * H ^ 2
  - βh * (2 * M ^ 2 / g ^ 2 + 2 * M / g * H + (1 / 2) * (H ^ 2 + φ0 ^ 2 + 2 * normSq φp))
  + 2 * M ^ 4 / g ^ 2 * alphaH M mh
  - g * M * alphaH M mh * (H ^ 3 + H * φ0 ^ 2 + 2 * H * normSq φp)
  - (1 / 8) * g ^ 2 * alphaH M mh *
      (H ^ 4 + φ0 ^ 4 + 4 * normSq φp ^ 2 + 4 * φ0 ^ 2 * normSq φp
        + 4 * H ^ 2 * normSq φp + 2 * φ0 ^ 2 * H ^ 2)

/-- The Higgs doublet `Φ = (φ⁺, (v + H + i φ⁰)/√2) ∈ ℂ²`. -/
noncomputable def higgsDoublet (g M H φ0 : ℝ) (φp : ℂ) : Fin 2 → ℂ :=
  ![φp, (((vev g M + H : ℝ) : ℂ) + (φ0 : ℂ) * I) / ((Real.sqrt 2 : ℝ) : ℂ)]

/-- The Hermitian square norm `Φ†Φ = |Φ₁|² + |Φ₂|²` of a doublet `Φ ∈ ℂ²`. -/
noncomputable def doubletNormSq (Φ : Fin 2 → ℂ) : ℝ := ∑ i, normSq (Φ i)

end SMHiggsPotential


