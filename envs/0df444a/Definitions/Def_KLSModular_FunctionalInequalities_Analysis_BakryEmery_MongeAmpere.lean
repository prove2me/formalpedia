-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:23:11.776043+00:00
-- url     : https://prove2.me/theorems/2b5c2043-7539-4080-9bb7-264ef25c0839
-- title:
--   Hessian matrix in an orthonormal basis
-- statement:
--   For a finite-dimensional real inner-product space $E$, a function $\varphi : E \to \mathbb{R}$, an orthonormal basis $b$ indexed by `Fin m`, and $x \in E$, `hessianMatrixIn φ b x` is the matrix with entries $D^2\varphi(x)(b_i,b_j)$. The module also contains supporting infrastructure for the Monge–Ampère log-determinant identities and positivity statements described in its header, but the listed declaration is this Hessian-coordinate definition.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Operator.Coordinates
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
--   import FunctionalInequalities.Analysis.Matrix.Positivity
--   import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
--   import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
--   import Mathlib.LinearAlgebra.Matrix.PosDef
--   import Mathlib.Analysis.Matrix.Normed
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def hessianMatrixIn {m : ℕ} (φ : E → ℝ) (b : OrthonormalBasis (Fin m) ℝ E) (x : E) :
--       Matrix (Fin m) (Fin m) ℝ :=
--     fun i j => bilinearIteratedFDerivTwo ℝ φ x (b i) (b j)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Matrix/DeterminantDerivative`](https://prove2.me/theorems/46a9a92e-982e-4a04-af01-9373c2e17873), [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Theorems in source order:
--
--   - [`hessianMatrixIn_posSemidef`](https://prove2.me/theorems/058f9921-bf17-4a55-978b-a367731b240a)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/MongeAmpere.lean) · `FunctionalInequalities.Analysis.BakryEmery.MongeAmpere` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/MongeAmpere.lean#L39-L42 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.MongeAmpere`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open FunctionalInequalities.Analysis
open Filter Topology
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- The Hessian matrix `(D²φ(x)(b i, b j))_{ij}` of `φ` in an orthonormal basis `b`. -/
def hessianMatrixIn {m : ℕ} (φ : E → ℝ) (b : OrthonormalBasis (Fin m) ℝ E) (x : E) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => bilinearIteratedFDerivTwo ℝ φ x (b i) (b j)
end BakryEmery
end Analysis
end FunctionalInequalities


