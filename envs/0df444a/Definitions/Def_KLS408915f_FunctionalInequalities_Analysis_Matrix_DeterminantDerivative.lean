-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
-- name    : KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:46:29.491721+00:00
-- url     : https://prove2.me/theorems/ed92cf5b-dd4f-4ebf-983d-75de36e0b842
-- title:
--   Continuous Multilinear Determinant Map
-- statement:
--   For a finite index type $ι$ with decidable equality, `detML` is the continuous multilinear map over $ℝ$ that takes a family of row vectors, equivalently a matrix $M : ι \to ι \to ℝ$, to its determinant. Its domain is the multilinear product of one copy of $ι \to ℝ$ for each row, and its codomain is $ℝ$. This bundle contains the determinant map used as a foundational object for later derivative and log-determinant formulas; it does not itself state such a derivative formula.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean#L25-L30 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.DeterminantDerivative`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Group.Matrix

noncomputable section
open scoped Matrix.Norms.Elementwise
namespace FunctionalInequalities
namespace Analysis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
 def detML : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := by
      change Continuous (fun M : ι → ι → ℝ => (Matrix.of M).det)
      simp only [Matrix.det_apply, Matrix.of_apply]
      fun_prop }
end Analysis
end FunctionalInequalities


