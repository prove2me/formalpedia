-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormula
-- name    : KLSModular_LevyStochCalc_Brownian_VectorItoFormula
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:29:30.251628+00:00
-- url     : https://prove2.me/theorems/fd5fe3af-3527-442e-9c98-db6ff7b03e09
-- title:
--   Uniform-grid error quantities for vector Itô formula
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `vectorItoGridResidue nR dR C T` is the explicit residual expression proportional to the second-derivative oscillation scale, while `vectorItoGridError nR dR B C T A K K₂ x` is the explicit real-valued error bound as a function of mesh parameter $x$, with terms for Taylor, drift, martingale, and quadratic-variation contributions. The definitions contain no assertion that these quantities converge or bound an error; those are separate declarations in the source module.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoFormulaDecomp
--   import LevyStochCalc.Brownian.VectorItoQuadVarRiemann
--   import LevyStochCalc.Brownian.VectorItoMartingaleRiemann
--   import LevyStochCalc.Brownian.ItoFormulaScalar
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def vectorItoGridResidue (nR dR C T : ℝ) : ℝ :=
--     nR * (2 * (dR ^ 2 * (C ^ 2 * T))) + 1 / 2 * (nR ^ 2 * (dR * C ^ 2 * T))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoFormulaDecomp`](https://prove2.me/theorems/8f8fed5f-bb75-4985-83e7-6765eeac8110), [`LevyStochCalc/Brownian/VectorItoQuadVarRiemann`](https://prove2.me/theorems/24682c26-cf5b-4b2c-9d08-792e82ae3217), [`LevyStochCalc/Brownian/VectorItoMartingaleRiemann`](https://prove2.me/theorems/a66fc89f-aa33-4950-8eab-8f30c14892aa), [`LevyStochCalc/Brownian/ItoFormulaScalar`](https://prove2.me/theorems/58932039-f65d-4b41-a617-bf3796b6492d).
--
--   Theorems in source order:
--
--   - [`IsVectorItoVersion.integral_abs_vectorItoFormula_le`](https://prove2.me/theorems/a8042955-1689-46eb-aed6-78c0655a75f1)
--   - [`IsVectorItoVersion.itoFormula`](https://prove2.me/theorems/9fc109b4-701c-4220-bf8e-2dcb0c672023)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoFormula.lean) · `LevyStochCalc.Brownian.VectorItoFormula` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoFormula.lean#L37-L66 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoFormula`, definition bundle `KLSModular_LevyStochCalc_Brownian_VectorItoFormula`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemann
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoMartingaleRiemann
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaScalar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormula.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
/-- The residue of the uniform-grid error that the oscillation scale `A` of the second derivative
leaves behind as the mesh vanishes, per unit of `A`. -/
noncomputable def vectorItoGridResidue (nR dR C T : ℝ) : ℝ :=
  nR * (2 * (dR ^ 2 * (C ^ 2 * T))) + 1 / 2 * (nR ^ 2 * (dR * C ^ 2 * T))
/-- The `L¹` error of the uniform-grid approximation in Itô's formula for a vector Itô process,
as a function of the mesh. The four summands are the Taylor remainder, the drift Riemann sums,
the martingale Riemann sums and the weighted quadratic variations; `A` and `K` are the two
constants of the affine oscillation bound `A + K‖z − w‖` on the second derivative. -/
noncomputable def vectorItoGridError (nR dR B C T A K K₂ : ℝ) (x : ℝ) : ℝ :=
  (A * (nR * (2 * (B ^ 2 * (T * x)) + 2 * (dR ^ 2 * (C ^ 2 * T))))
      + K * (nR ^ 2 * (nR * (4 * (B ^ 3 * T * x ^ 2
        + dR ^ 2 * (dR * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt x))))))))
    + nR * (K₂ * B * (T * (nR * (B * x + dR * (C * Real.sqrt x)))))
    + nR * dR * Real.sqrt (C ^ 2 * (K₂ ^ 2
        * (T * (nR * (2 * (B * x) ^ 2 + 2 * (dR ^ 2 * (C ^ 2 * x)))))))
    + 1 / 2 * (nR ^ 2 * (K₂ * B ^ 2 * T * x
        + 2 * (K₂ * B * dR * C * T * Real.sqrt x)
        + dR * Real.sqrt (K₂ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * x))
        + dR ^ 2 * Real.sqrt (K₂ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
            * (T * x))
        + (A * (dR * C ^ 2) * T
          + K * (dR * C ^ 2) * (T * (nR * (B * x + dR * (C * Real.sqrt x)))))))
end Ito
end Brownian
end LevyStochCalc


