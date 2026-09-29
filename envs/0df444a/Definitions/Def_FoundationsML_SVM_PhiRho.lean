-- Prove2me | Definitions.Def_FoundationsML_SVM_PhiRho
-- name    : FoundationsML_SVM_PhiRho
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:25:34.081983+00:00
-- url     : https://prove2.me/theorems/943e3bec-a322-432c-8ae6-bb9ef5846173
-- title:
--   The rho-margin loss function (Definition 5.5)
-- statement:
--   **Definition 5.5 (Margin loss function), p. 92, PDF p. 109.** For any $\rho>0$, the
--   $\rho$-margin loss is the function $L_\rho:\mathbb R\times\mathbb R\to\mathbb R_+$ defined
--   for all $y,y'\in\mathbb R$ by $L_\rho(y,y')=\Phi_\rho(yy')$, with
--   $$\Phi_\rho(x)=\min\Big(1,\max\Big(0,1-\frac x\rho\Big)\Big) =
--     \begin{cases} 1 & x\le 0\\ 1-\frac x\rho & 0\le x\le \rho\\ 0 & \rho\le x.\end{cases}$$
--
--   **Formalization Note.** Only $\Phi_\rho$ is named as a definition; $L_\rho(y,y')=\Phi_\rho(y
--   y')$ is folded directly into `EmpiricalMarginLoss` rather than declared separately, since
--   it is never used on its own elsewhere in the chapter.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 92, Definition 5.5 (PDF p. 109)

import Mathlib

namespace FoundationsML.SVM

/-- The `ρ`-margin loss function `Φ_ρ` (Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, Definition 5.5, p. 92, PDF p. 109):
`Φ_ρ(x) = min(1, max(0, 1 − x/ρ))`, i.e. `1` for `x ≤ 0`, `1 − x/ρ` for `0 ≤ x ≤ ρ`, and `0`
for `ρ ≤ x`. The `ρ`-margin loss `L_ρ(y, y′) = Φ_ρ(y·y′)` of Definition 5.5 is folded directly
into `EmpiricalMarginLoss` rather than named separately. -/
noncomputable def PhiRho (ρ : ℝ) (x : ℝ) : ℝ := min 1 (max 0 (1 - x / ρ))

end FoundationsML.SVM


