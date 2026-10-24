-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
-- name    : KLS408915f_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:59:04.554301+00:00
-- url     : https://prove2.me/theorems/e74988a2-e63f-4ba4-a199-7febd19f3b4c
-- title:
--   Coordinate trace and Hilbert–Schmidt square norm
-- statement:
--   `stdTrace M` is the trace of a continuous operator $M$ on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$ computed in the standard basis: $\sum_i\langle e_i,Me_i\rangle$. `hsNormSq M` is the squared Hilbert–Schmidt norm $\sum_i\sum_j\langle e_i,Me_j\rangle^2$. Both are real-valued finite sums and require no positivity or symmetry assumption on $M$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L54-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Operator_HilbertSchmidt`; the repository is private at upload time).

import Mathlib
import Mathlib.Analysis.InnerProductSpace.Trace

noncomputable section
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
variable {n : ℕ}
/-- The coordinate trace `tr M = Σ_i ⟪e_i, M e_i⟫` of an operator on `ℝⁿ`. -/
def stdTrace (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, M (EuclideanSpace.basisFun (Fin n) ℝ i)⟫
/-- The squared Hilbert–Schmidt norm `‖M‖²_HS = Σ_{i,j} ⟪e_i, M e_j⟫²`. -/
def hsNormSq (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ∑ j, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, M (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ^ 2
end Analysis
end FunctionalInequalities


