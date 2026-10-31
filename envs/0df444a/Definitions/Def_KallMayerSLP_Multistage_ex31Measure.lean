-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ex31Measure
-- name    : KallMayerSLP_Multistage_ex31Measure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:46.956813+00:00
-- url     : https://prove2.me/theorems/114c03c6-afd7-4b50-aa72-22bb75473984
-- title:
--   Example 3.1: the joint distribution
-- statement:
--   The joint distribution $\mathbb P_\zeta$ of $\zeta=(\xi_2,\xi_3)$ in Example 3.1: the measure on $\mathbb R^2$ with density $f(\xi_2,\xi_3)$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, p.257 (PDF 266)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ex31Density

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- The joint distribution `ℙ_ζ` of `ζ = (ξ_2, ξ_3)` of Example 3.1 (Kall & Mayer, *Stochastic
Linear Programming* (2005), Chapter 3, Example 3.1, p.257, PDF 266), the measure on `ℝ²` with
density `ex31Density ε`. -/
noncomputable def ex31Measure (ε : ℝ) : Measure (ℝ × ℝ) :=
  volume.withDensity fun p => ENNReal.ofReal (ex31Density ε p.1 p.2)

end KallMayerSLP.Multistage


