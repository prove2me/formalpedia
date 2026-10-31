-- Prove2me | Definitions.Def_TargetSupplyChain_ClosedForms
-- name    : TargetSupplyChain_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:21:38.421992+00:00
-- url     : https://prove2.me/theorems/09fc595b-1fc4-40c6-9c8a-550cedcd65ee
-- title:
--   The thresholds $\alpha^{r1}_{nt}$, $\alpha^{r2}_{nt}$ and the interior decisions $w^1_{nt}$, $y^1_{nt}$ (p.12)
-- statement:
--   The closed-form quantities named before Proposition 2, transcribed from p.12:
--   $$
--   \alpha^{r1}_{nt}=\frac{3p(a+b)-\sqrt{p^2(a+b)^2+4pb^2(p+c)}}{4p},\qquad \alpha^{r2}_{nt}=\frac{(p-c)(a+b)}{3p-c},
--   $$
--   $$
--   w^1_{nt}=\sqrt{\frac{2p(p+c)(a+b-\alpha^r)}{a+b-2\alpha^r}}-p,\qquad y^1_{nt}=\sqrt{\frac{2p(a+b-\alpha^r)(a+b-2\alpha^r)}{p+c}}-(a+b-2\alpha^r).
--   $$
--   When $b/a>2/\xi^c$, the thresholds split the target range into the three regimes of Proposition 2, and $(w^1_{nt},y^1_{nt})$ is the NT decision pair in the middle regime $[\alpha^{r1}_{nt},\alpha^{r2}_{nt})$.
--
--   **Formalization Note** These are formulas only; that they are the NT decisions is the content of Proposition 2. $w^1_{nt}$ is used only for $\alpha^r<\alpha^{r2}_{nt}<(a+b)/3$, where $a+b-2\alpha^r>0$.
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), §4.2, definitions before Proposition 2, p.12

import Mathlib
import Definitions.Def_TargetSupplyChain_Model

namespace TargetSupplyChain

/-- The threshold `αʳ¹_nt = (3p(a+b) − √(p²(a+b)² + 4pb²(p+c)))/(4p)` named before
Proposition 2, Chen–Tang, *Supply Chain Performance with Target-Oriented Firms*,
SSRN 3533746 (version of July 6, 2021), §4.2, p.12. Transcribed. -/
noncomputable def alphaR1 (P : Params) : ℝ :=
  (3 * P.p * (P.a + P.b) -
      Real.sqrt (P.p ^ 2 * (P.a + P.b) ^ 2 + 4 * P.p * P.b ^ 2 * (P.p + P.c))) / (4 * P.p)

/-- The threshold `αʳ²_nt = (p − c)(a + b)/(3p − c)`, §4.2, p.12. Transcribed. -/
noncomputable def alphaR2 (P : Params) : ℝ :=
  (P.p - P.c) * (P.a + P.b) / (3 * P.p - P.c)

/-- The interior wholesale price `w¹_nt = √(2p(p+c)(a+b−αʳ)/(a+b−2αʳ)) − p`, §4.2, p.12.
Transcribed.

**Formalization Note** It is used only for `αʳ ∈ [αʳ¹_nt, αʳ²_nt)`, where
`αʳ < αʳ²_nt < (a + b)/3`, so the denominator `a + b − 2αʳ` is positive there. -/
noncomputable def w1nt (P : Params) (α : ℝ) : ℝ :=
  Real.sqrt (2 * P.p * (P.p + P.c) * (P.a + P.b - α) / (P.a + P.b - 2 * α)) - P.p

/-- The interior order quantity `y¹_nt = √(2p(a+b−αʳ)(a+b−2αʳ)/(p+c)) − (a + b − 2αʳ)`,
§4.2, p.12. Transcribed. -/
noncomputable def y1nt (P : Params) (α : ℝ) : ℝ :=
  Real.sqrt (2 * P.p * (P.a + P.b - α) * (P.a + P.b - 2 * α) / (P.p + P.c)) -
    (P.a + P.b - 2 * α)

end TargetSupplyChain


