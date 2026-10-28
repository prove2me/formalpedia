-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity
-- name    : KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:21:33.655182+00:00
-- url     : https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c
-- title:
--   Matrix-entry coordinates and quadratic floors
-- statement:
--   `FunctionalInequalities.Analysis.matrixEntries` views a real matrix as an element of the Euclidean space indexed by pairs of indices, using the Frobenius-coordinate representation. `QuadraticFloor A a` means that $a\sum_i v_i^2\le v\,\mathbin{\text{⬝ᵥ}}\,(A\,\mathbin{\text{*ᵥ}}\,v)$ for every coordinate vector v. The private `outer` definition forms the matrix with entries $v_i v_j$.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Matrix.Order
--   import Mathlib.Analysis.Matrix.PosDef
--   import Mathlib.LinearAlgebra.Matrix.Kronecker
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.CStarAlgebra.Matrix
--   import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
--   import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def matrixEntries (A : Matrix ι ι ℝ) : EuclideanSpace ℝ (ι × ι) :=
--     WithLp.toLp 2 (fun ij => A ij.1 ij.2)
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`posSemidef_weightedGram`](https://prove2.me/theorems/b7c15040-db81-4850-95bc-cc1e4b6e1569)
--   - [`exists_quadraticFloor_of_posDef`](https://prove2.me/theorems/151ec180-9404-48fb-af6c-ada52b2eac65)
--   - [`root_difference_bound`](https://prove2.me/theorems/45094b81-6a32-4174-a33a-b96d1b6184f4)
--   - [`inverse_quadratic_young`](https://prove2.me/theorems/88b8a40a-52a8-4842-a7d8-a36165a50c94)
--   - [`trace_mul_nonneg`](https://prove2.me/theorems/8f84fe39-fbf6-4934-8c39-8242968c3544)
--   - [`traceGram_posSemidef`](https://prove2.me/theorems/244506ec-0037-4420-8e3c-8acdf6db2119)
--   - [`trace_forcing_add_twice_energy_nonneg`](https://prove2.me/theorems/880bf0da-cd46-42c8-89a4-a8d488e0bf20)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean) · `FunctionalInequalities.Analysis.Matrix.Positivity` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L77-L147 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity`; the repository is private at upload time).

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

noncomputable section
open scoped MatrixOrder Kronecker
namespace FunctionalInequalities
namespace Analysis
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
section Frobenius
open Matrix Finset
open scoped RealInnerProductSpace
/-- Euclidean view of the matrix entries; its norm is the Frobenius norm. -/
def matrixEntries (A : Matrix ι ι ℝ) : EuclideanSpace ℝ (ι × ι) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)
end Frobenius
section Floor
open Matrix Finset
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
/-- A quadratic lower floor `a ‖v‖² ≤ ⟪v, A v⟫` in coordinates. -/
def QuadraticFloor (A : Matrix ι ι ℝ) (a : ℝ) : Prop :=
  ∀ v : ι → ℝ, a * (∑ i, (v i) ^ 2) ≤ v ⬝ᵥ (A *ᵥ v)
variable [DecidableEq ι]
 def outer (v : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i * v j
end Floor
end Analysis
end FunctionalInequalities


