-- Prove2me | Definitions.Def_GuoZhaoADRC_Pi4
-- name    : GuoZhaoADRC_Pi4
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:42.725253+00:00
-- url     : https://prove2.me/theorems/50622cb1-94f4-4ce1-b018-87e46335cb3f
-- title:
--   $\Pi_4=\sum_i(\beta^i_2(L_i+1)+\beta^i_1\Xi^i_2)$ (3.14), corrected
-- statement:
--   For constants $\Xi^1_2,\dots,\Xi^m_2$ (those of (3.9)),
--
--   $$\Pi_4=\sum_{i=1}^m\bigl(\beta^i_2(L_i+1)+\beta^i_1\Xi^i_2\bigr),$$
--
--   the coefficient of $\|e\|\,\|\eta\|$ in the bound (3.15) on the derivative of $V$.
--
--   **Formalization Note** The page prints $\Pi_4=\sum_i\beta^i_2(L_i+1)$. The passage from (3.12) to (3.13) drops the term $\beta^i_1\|e^i\|\,\Xi^i_2\|\eta\|$ of (3.12), which also contributes to the $\|e\|\,\|\eta\|$ coefficient; with the printed $\Pi_4$ the bound (3.15) does not follow from (3.12) whenever $\beta^i_1\Xi^i_2>0$.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.14), p.1739 (with (3.12)–(3.13))

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData

namespace GuoZhaoADRC

/-- **`Π₄ = ∑_i (β^i_2(L_i + 1) + β^i_1 Ξ^i_2)` (corrected).**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.14), p.1739.

**Formalization Note.** The page prints `Π₄ = ∑_i β^i_2(L_i + 1)`: the step from (3.12) to (3.13)
drops the term `β^i_1 ‖e^i‖ Ξ^i_2 ‖η‖` of (3.12), which belongs to the `‖e‖‖η‖` coefficient.
The constants `Ξ^i_2` of (3.9) are an argument. -/
noncomputable def Pi4 {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s)
    (Ξ₂ : Fin m → ℝ) : ℝ :=
  ∑ i, (D.beta2 i * ((D.L i : ℝ) + 1) + D.beta1 i * Ξ₂ i)

end GuoZhaoADRC


