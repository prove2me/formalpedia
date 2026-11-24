-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_theorem4Counterexample
-- name    : GenEmpLik_Coverage_Supplement_theorem4Counterexample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:18:23.831947+00:00
-- url     : https://prove2.me/theorems/63439def-602a-46b9-9ead-3299bcd1c008
-- title:
--   Rademacher quadratic-loss model exposing the zero-variance failure of Theorem 4
-- statement:
--   Let $P_0$ be the Rademacher law, uniform on $\{-1,1\}$, let $X=[-1,1]\subset\mathbb R^1$, and let
--   $$\ell(x;\xi)=x^2+x\xi .$$
--   The population risk is $E_{P_0}\ell(x;\xi)=x^2$, with the unique minimizer $x^\star=0$, and $\ell(0;\xi)=0$ for every $\xi$, so the optimal loss has variance zero. The loss is $3$-Lipschitz on $X$ for every $\xi$. This model supplies a counterexample to Theorem 4 as printed; it is not asserted to be a construction from the paper.
--
--   **Formalization Note** The two atoms are coded by `Fin 2` with $\xi=2j-1$; the decision space is `EuclideanSpace ℝ (Fin 1)` and $x$ is its coordinate `x 0`.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 9, Theorem 4; proof p. 40 (Appendix C.3); counterexample model (not a source construction)

import Mathlib

open MeasureTheory

namespace GenEmpLik.Coverage.Supplement

/-- Rademacher population for the failure of Theorem 4 as printed, p. 9.
`Fin 2` is coded by ξ = 2j - 1, with equal probabilities on {-1, 1}. -/
noncomputable def rademacherLaw : Measure (Fin 2) :=
  (PMF.uniformOfFintype (Fin 2)).toMeasure

/-- The sign coded by `j : Fin 2`: ξ = 2j - 1. -/
def rademacherValue (j : Fin 2) : ℝ := 2 * (j : ℝ) - 1

/-- The compact decision set X = [-1, 1] in ℝ¹. -/
def symmetricUnitInterval : Set (EuclideanSpace ℝ (Fin 1)) := {x | |x 0| ≤ 1}

/-- The loss ℓ(x; ξ) = x² + x ξ. Its population risk x² has the unique minimizer 0,
where the loss is identically 0, so the optimal loss has variance zero. -/
def degenerateLoss (x : EuclideanSpace ℝ (Fin 1)) (j : Fin 2) : ℝ :=
  x 0 ^ 2 + x 0 * rademacherValue j

end GenEmpLik.Coverage.Supplement


