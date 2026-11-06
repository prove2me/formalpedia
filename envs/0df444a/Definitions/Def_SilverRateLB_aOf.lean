-- Prove2me | Definitions.Def_SilverRateLB_aOf
-- name    : SilverRateLB_aOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:13.029791+00:00
-- url     : https://prove2.me/theorems/80095cf0-eafa-409f-a073-f6f6802083e7
-- title:
--   The constants $c$, $R$ and $a$ of Lemma 2.4
-- statement:
--   For parameters $\varepsilon,\gamma>0$ set
--   $$c := \sqrt{1+2\gamma+\varepsilon^2},\qquad R := \sqrt{\varepsilon^2+(1+\gamma)^2},$$
--   $$a := \max\Bigl\{2,\ \frac2c\Bigl(\varepsilon+\varepsilon^{-1}\Bigl[\frac{c(1+\gamma+R)}{\varepsilon(\gamma+R)}\Bigr]^{R/\gamma}\Bigr)\Bigr\}.$$
--   $R$ is the radius of the circle centred at $(0,\gamma)$ through $(\varepsilon,-1)$, which meets the positive horizontal axis at $(c,0)$. The constant $c$ is the coefficient of the gap mass in the transfer ratio $(b_i-2)/(c(a+s_i))$, and $a$ is its additive offset.
--
--   **Formalization Note** The page prints the factor $2/c$; §B.4 writes the same constant as $\max\{2,2C_0/c\}$ with $C_0=\varepsilon+(H_0+1)/\varepsilon$, $H_0=[c(1+\gamma+R)/(\varepsilon(\gamma+R))]^{R/\gamma}-1$.
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma 2.4, p. 11; §B.4, p. 30

import Mathlib

namespace SilverRateLB

/-- The constant `c := √(1 + 2γ + ε²)` of Lemma 2.4 (p. 11). -/
noncomputable def cOf (ε γ : ℝ) : ℝ := Real.sqrt (1 + 2 * γ + ε ^ 2)

/-- The radius `R := √(ε² + (1 + γ)²)` of Lemma 2.4 (p. 11): the circle centred at `(0, γ)`
through `(ε, −1)`. -/
noncomputable def ROf (ε γ : ℝ) : ℝ := Real.sqrt (ε ^ 2 + (1 + γ) ^ 2)

/-- **The constant `a` of Lemma 2.4**:
`a = max{2, (2/c)(ε + ε⁻¹[c(1+γ+R)/(ε(γ+R))]^{R/γ})}` with `c = cOf ε γ`, `R = ROf ε γ`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma 2.4,
p. 11: "Fix ε, γ > 0 and let c := √(1+2γ+ε²) and R := √(ε²+(1+γ)²). … where
a = max{2, (2/c)(ε + ε⁻¹[c(1+γ+R)/(ε(γ+R))]^{R/γ})}." The same constant is written in §B.4,
p. 30, as `H₀ := [c(1+γ+R)/(ε(γ+R))]^{R/γ} − 1`, `C₀ := ε + (H₀+1)/ε`, `a := max{2, 2C₀/c}`.

**Formalization Note** The factor is `2/c` (the page prints a fraction; the text layer of the PDF
loses it). The power is `Real.rpow`; it is used only for `ε, γ > 0`, where the base is positive. -/
noncomputable def aOf (ε γ : ℝ) : ℝ :=
  max 2 ((2 / cOf ε γ) * (ε + ε⁻¹ *
    ((cOf ε γ * (1 + γ + ROf ε γ)) / (ε * (γ + ROf ε γ))) ^ (ROf ε γ / γ)))

end SilverRateLB


