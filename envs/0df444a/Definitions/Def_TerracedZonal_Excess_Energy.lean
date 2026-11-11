-- Prove2me | Definitions.Def_TerracedZonal_Excess_Energy
-- name    : TerracedZonal_Excess_Energy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:02:35.365348+00:00
-- url     : https://prove2.me/theorems/40619092-5c5f-44ec-b37d-f9ffb1f4321d
-- title:
--   Logarithmic energy on $S^2$ and the Brauchart–Hardin–Saff benchmark $E_{\mathrm{BHS}}(N)$
-- statement:
--   For finitely many points $x_1,\dots,x_N\in\mathbb R^3$ the **logarithmic energy** is
--
--   $$E(X_N)=\sum_{1\le i<j\le N}\log\frac{1}{\|x_i-x_j\|},$$
--
--   each unordered pair counted once (the single-counted convention; much of the literature uses twice this). The **Brauchart–Hardin–Saff benchmark** is
--
--   $$E_{\mathrm{BHS}}(N)=\tfrac12\big(\tfrac12-\log 2\big)N^2-\tfrac14 N\log N+\tfrac12 C_{\mathrm{BHS}}N,\qquad C_{\mathrm{BHS}}=2\log2+\tfrac12\log\tfrac23+3\log\frac{\sqrt\pi}{\Gamma(1/3)}\approx-0.0556053,$$
--
--   with natural logarithms. $C_{\mathrm{BHS}}$ is the regularized Epstein zeta constant of the unit-density triangular lattice, and $E_{\mathrm{BHS}}(N)$ is the conjectured minimal energy up to $o(N)$. The excess $E(X_N)-E_{\mathrm{BHS}}(N)$ is the quantity bounded in Theorem 4.3.
--
--   **Formalization Note** The energy is defined for any finite indexed family of points as half the sum of $\log(1/\|x_i-x_j\|)$ over ordered pairs $i\ne j$, which equals the sum over unordered pairs. Coincident points would contribute $\log(1/0)=0$ in Lean; the TerracedZonal configurations have pairwise distinct points.
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), eq. (1) p. 1 (PDF 2), eq. (2) p. 1 (PDF 2), eq. (16) p. 16 (PDF 17)

import Mathlib

namespace TerracedZonal.Excess

open Real

/-- Logarithmic energy (1), p. 1 (PDF 2), of a finite indexed point family in `ℝ³`:
`E(X) = ∑_{i<j} log (1/‖xᵢ - xⱼ‖)`, written as half the sum over ordered pairs `i ≠ j`
(each unordered pair counted once, the paper's single-counted convention, App. A.1). -/
noncomputable def logEnergy {ι : Type*} [Fintype ι] (X : ι → EuclideanSpace ℝ (Fin 3)) : ℝ := by
  classical
  exact (1 / 2 : ℝ) * ∑ i, ∑ j, if i = j then (0 : ℝ) else Real.log (1 / ‖X i - X j‖)

/-- The Brauchart–Hardin–Saff constant, closed form (16), p. 16 (PDF 17):
`C_BHS = 2 log 2 + ½ log (2/3) + 3 log (√π / Γ(1/3))`. -/
noncomputable def C_BHS : ℝ :=
  2 * Real.log 2 + (1 / 2) * Real.log (2 / 3) + 3 * Real.log (Real.sqrt π / Real.Gamma (1 / 3))

/-- The BHS benchmark (2), p. 1 (PDF 2):
`E_BHS(N) = ½(½ - log 2) N² - ¼ N log N + ½ C_BHS N` (natural logarithm). -/
noncomputable def E_BHS (N : ℕ) : ℝ :=
  (1 / 2) * (1 / 2 - Real.log 2) * (N : ℝ) ^ 2 - (1 / 4) * (N : ℝ) * Real.log (N : ℝ)
    + (1 / 2) * C_BHS * (N : ℝ)

end TerracedZonal.Excess


