-- Prove2me | Definitions.Def_LevyExtrema_SBA_eta
-- name    : LevyExtrema_SBA_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:17.83098+00:00
-- url     : https://prove2.me/theorems/4695097e-2333-47f1-b475-cd62d6e7ad29
-- title:
--   The geometric rate $\eta_p=1+\mathbb 1_{\{p>\alpha\}}+(p/\alpha_+)\mathbb 1_{\{p\le\alpha\}}$ (4.22)
-- statement:
--   For $p>0$ the **rate** of Theorem 2 is
--
--   $$\eta_p=1+\mathbb 1_{\{p>\alpha\}}+\frac{p}{\alpha_+}\cdot\mathbb 1_{\{p\le\alpha\}}\in(1,2].\tag{4.22}$$
--
--   The paper notes that $\eta_p\ge3/2$ for $p\ge1$. The $L^p$-errors of the stick-breaking approximation of the supremum decay like $\eta_p^{-n}$.
--
--   **Formalization Note** The division by $\alpha_+$ occurs only in the branch $p\le\alpha$; there $\alpha_+\ge\alpha\ge p>0$.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (4.22), p. 24

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_alpha

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **The geometric rate η_p**, (4.22).
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (4.22), p. 24:
"η_p = 1 + 1{p>α} + (p/α₊) · 1{p≤α} ∈ (1, 2], for any p > 0".

**Formalization Note.** The division `p / α₊` occurs only in the branch `p ≤ α`; under
"not compound Poisson with drift", α₊ > 0 (p. 24), so no division by zero occurs there. -/
noncomputable def eta (Tr : Triplet) (δ p : ℝ) : ℝ :=
  1 + (if alpha Tr < p then 1 else 0) + (if p ≤ alpha Tr then p / alphaPlus Tr δ else 0)

end LevyExtrema.SBA


