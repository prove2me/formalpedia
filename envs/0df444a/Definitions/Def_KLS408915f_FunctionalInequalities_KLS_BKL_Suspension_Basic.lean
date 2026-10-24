-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
-- name    : KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:54:31.724291+00:00
-- url     : https://prove2.me/theorems/d38b9c68-d0ca-4c28-9a3e-73a72ec99a41
-- title:
--   Finite-copy suspension potential
-- statement:
--   For a potential $V:E\to\mathbb{R}$, function $f:E\to\mathbb{R}$, real parameters $\beta,\sigma$, copy count $N$, and point $(s,x_1,\ldots,x_N)$, `potential V f beta sigma N` is $\sum_iV(x_i)+\beta\left|\sigma s-\frac{\sum_i f(x_i)}{\sqrt N}\right|$. The definition is made on $\mathbb{R}\times(\mathrm{Fin}\,N\to E)$ and does not impose positivity of $\beta$, a relation between $\sigma$ and $\beta$, or convexity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean#L24-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Basic`, definition bundle `KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace Suspension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The potential (109) on one auxiliary coordinate and `N` copies of the original space.
In the paper `sigma = sqrt (1 + 2 / beta²)`. Convexity holds for every real `sigma`. -/
def potential (V f : E → ℝ) (beta sigma : ℝ) (N : ℕ) (p : ℝ × (Fin N → E)) : ℝ :=
  (∑ i, V (p.2 i)) + beta * |sigma * p.1 - (∑ i, f (p.2 i)) / Real.sqrt N|
end Suspension
end LogConcave
end KLS
end FunctionalInequalities


