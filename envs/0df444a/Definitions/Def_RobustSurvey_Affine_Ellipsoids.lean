-- Prove2me | Definitions.Def_RobustSurvey_Affine_Ellipsoids
-- name    : RobustSurvey_Affine_Ellipsoids
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:01:11.170295+00:00
-- url     : https://prove2.me/theorems/e286d10d-efd9-4fb7-b847-bdba628b5bbb
-- title:
--   Centered ellipsoidal uncertainty and the rank factor
-- statement:
--   Let $S_1,\ldots,S_K$ be real symmetric positive semidefinite $L\times L$ matrices. For a positive radius $\rho$, their centered quadratic uncertainty set is
--   $$U_\rho=\{u\in\mathbb R^L:\ u^T(\rho^{-2}S_k)u\le1\text{ for every }1\le k\le K\}.$$
--   Singular and redundant members are allowed; the intersection may be unbounded. Define $r=\sum_k\operatorname{rank}_{\mathbb R}(S_k)$ and, when $r>0$,
--   $$\gamma=\sqrt{2\ln(6r)}.$$
--   Positive semidefiniteness includes symmetry. The real logarithm is natural, the finite matrix ranks are natural numbers coerced to real numbers, and $\rho^{-2}$ is represented as $(\rho^2)^{-1}$. The definitions are total in Lean, but the mission's theorems use only $\rho>0$ and Theorem 7 additionally uses $r>0$; no assertion relies on a default value for a reciprocal at zero or a logarithm at zero. Theorem 6 does not need the rank restriction.
-- source:
--   Bertsimas, Brown and Caramanis, Theory and Applications of Robust Optimization, held PDF marked arXiv:1010.5445v1 (2010), https://arxiv.org/abs/1010.5445v1; SHA-256 25714e004b9b868fcb48997d3364800e379cd1be5f8b027ca6f50ee08f25ae50; anomalous revised-version date November 26, 2024; Theorems 6–7 and the gamma display, printed pp. 25–26 / PDF pp. 26–27.

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators
open Matrix

namespace RobustSurvey.Affine

/-- A finite family of centered ellipsoidal quadratic inequalities; singular members allowed. -/
structure Ellipsoids (L K : ℕ) where
  S : Fin K → Matrix (Fin L) (Fin L) ℝ
  psd : ∀ k, (S k).PosSemidef

/-- Used at positive radii in the statements: uᵀ(ρ⁻² Sₖ)u ≤ 1 for each k. -/
def Ellipsoids.uncertainty {L K : ℕ} (E : Ellipsoids L K) (ρ : ℝ) :
    Set (Fin L → ℝ) :=
  {u | ∀ k, u ⬝ᵥ (((ρ ^ 2)⁻¹ • E.S k) *ᵥ u) ≤ 1}

noncomputable def Ellipsoids.rankSum {L K : ℕ} (E : Ellipsoids L K) : ℕ :=
  ∑ k, (E.S k).rank

/-- The displayed factor, used only with positive rank sum. -/
noncomputable def Ellipsoids.gamma {L K : ℕ} (E : Ellipsoids L K) : ℝ :=
  Real.sqrt (2 * Real.log (6 * (E.rankSum : ℝ)))

end RobustSurvey.Affine


