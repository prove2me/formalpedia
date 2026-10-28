-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
-- name    : KLSModular_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:21:45.404298+00:00
-- url     : https://prove2.me/theorems/46a9a92e-982e-4a04-af01-9373c2e17873
-- title:
--   Continuous Multilinear Determinant Map
-- statement:
--   For a finite index type $ι$ with decidable equality, `detML` is the continuous multilinear map over $ℝ$ that takes a family of row vectors, equivalently a matrix $M : ι \to ι \to ℝ$, to its determinant. Its domain is the multilinear product of one copy of $ι \to ℝ$ for each row, and its codomain is $ℝ$. This bundle contains the determinant map used as a foundational object for later derivative and log-determinant formulas; it does not itself state such a derivative formula.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Calculus.FDeriv.Analytic
--   import Mathlib.Topology.Algebra.Group.Matrix
--   import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
--   import Mathlib.LinearAlgebra.Matrix.Trace
--   import Mathlib.Analysis.Matrix.Normed
--   import Mathlib.Analysis.SpecialFunctions.Log.Deriv
--   import Mathlib.Analysis.Calculus.TaylorIntegral
--   import Mathlib.Analysis.Matrix.PosDef
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def detML : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
--     { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
--       cont := by
--         change Continuous (fun M : ι → ι → ℝ => (Matrix.of M).det)
--         simp only [Matrix.det_apply, Matrix.of_apply]
--         fun_prop }
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`fderiv_det_eq_det_mul_trace`](https://prove2.me/theorems/7b944e90-ac35-4a2d-a68e-0c989cf61604)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean) · `FunctionalInequalities.Analysis.Matrix.DeterminantDerivative` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean#L25-L30 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.DeterminantDerivative`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Matrix.PosDef

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


