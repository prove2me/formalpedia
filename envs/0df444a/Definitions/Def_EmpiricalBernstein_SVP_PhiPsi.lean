-- Prove2me | Definitions.Def_EmpiricalBernstein_SVP_PhiPsi
-- name    : EmpiricalBernstein_SVP_PhiPsi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:48.769745+00:00
-- url     : https://prove2.me/theorems/ec5531d1-be65-4b1a-93c7-d31c893f2378
-- title:
--   Sec. 3, p. 5 — the functions $\Phi(x,t)$ and $\Psi(x,t)$
-- statement:
--   For $x \in [0,1]^n$ and $t \ge 0$ define
--
--   $$
--   \Phi(x,t) = P_n(x) + \sqrt{\frac{2V_n(x)\,t}{n}} + \frac{7t}{3(n-1)}, \qquad
--   \Psi(x,t) = P_n(x) + \sqrt{\frac{18V_n(x)\,t}{n}} + \frac{11t}{n-1},
--   $$
--
--   where $P_n(x) = \frac1n\sum_i x_i$ is the sample mean and $V_n(x)$ the sample variance.
--
--   $\Phi(x,t)$ is the empirical Bernstein upper confidence bound on the mean at confidence level $1 - 2e^{-t}$; $\Psi$ is a looser version of it. Comparing them on the two halves of a double sample is the key step in extending the empirical Bernstein bound to infinite function classes.
--
--   **Formalization Note** Both are defined on all of `Fin n → ℝ` and all real $t$; the theorems restrict to $x\in[0,1]^n$, $t$ as on the page, and $n \ge 2$.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Sec. 3, p. 5

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar

namespace EmpiricalBernstein.SVP

open VarianceRegularization.Expansion

/-- `Φ(x, t) = P_n(x) + √(2 V_n(x) t / n) + 7t / (3(n − 1))` (arXiv:0907.3740v1, Sec. 3, p. 5). -/
noncomputable def Phi {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  empMean x + Real.sqrt (2 * sampleVar x * t / n) + 7 * t / (3 * ((n : ℝ) - 1))

/-- `Ψ(x, t) = P_n(x) + √(18 V_n(x) t / n) + 11t / (n − 1)` (arXiv:0907.3740v1, Sec. 3, p. 5). -/
noncomputable def Psi {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  empMean x + Real.sqrt (18 * sampleVar x * t / n) + 11 * t / ((n : ℝ) - 1)

end EmpiricalBernstein.SVP


