-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:50:55.841808+00:00
-- url     : https://prove2.me/theorems/86db9ab2-0c2a-4dff-8904-eff1bba339a8
-- title:
--   Coordinate densities for weak inverse-Hessian identities
-- statement:
--   For functions on `EuclideanSpace ℝ (Fin n)`, `coord f i x` is the directional derivative $Df(x)[e_i]$, `weightedTest u a f i x` is $a(x)e^{-u(x)}\,\operatorname{coord}(f,i,x)$, and `energyDensity u a f x` is $e^{-u(x)}$ times the inverse-Hessian contraction $\sum_{i,j}(\nabla^2u(x))^{-1}_{ij}\,\operatorname{coord}(a,i,x)\operatorname{coord}(f,j,x)$. `generatorDensity u V a f x` is $a(x)e^{-u(x)}$ times $\operatorname{tr}((\nabla^2u(x))^{-1}\nabla^2f(x))-DV(\nabla u(x))[\nabla f(x)]$. These private definitions support the weak integration-by-parts identities; the displayed bundle does not change their stated measurability or regularity assumptions.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Matrix.WeakDerivative
--   import FunctionalInequalities.Analysis.Matrix.Piola
--   import FunctionalInequalities.Analysis.Cutoff.LipschitzBall
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.Analysis.WeakDerivative.Calculus
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import Mathlib.Analysis.Calculus.Rademacher
--   import Mathlib.LinearAlgebra.Matrix.Hermitian
--   import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
--   import Mathlib.LinearAlgebra.Matrix.Trace
--   import Mathlib.Data.Real.Star
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private abbrev coord {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
--       (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
--     fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681), [`Analysis/Matrix/Piola`](https://prove2.me/theorems/bafaf8f6-610f-44ba-81ae-c118558a1200), [`Analysis/Cutoff/LipschitzBall`](https://prove2.me/theorems/ff179ecc-cd31-4939-9396-b1ea0665ce64), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799).
--
--   Theorems in source order:
--
--   - [`ae_fderiv_mongeAmpere_exponent`](https://prove2.me/theorems/71049741-6710-4957-9e2a-2a505bfab529)
--   - [`sum_inv_gradient_test_sub_chain_eq`](https://prove2.me/theorems/7266b246-03c7-419d-a30f-6d99183cc1fc)
--   - [`smooth_test_derivative`](https://prove2.me/theorems/a020d053-5b2e-45e7-bfaf-a25b6c53786c)
--   - [`assemble_generator`](https://prove2.me/theorems/ecbe4dd5-bf64-4880-91be-e99fda5c9cf6)
--   - [`integral_mul_generator_eq_neg_energy`](https://prove2.me/theorems/eb1196e2-8044-4e2b-9000-8fcc401166ec)
--   - [`integral_mul_generator_eq_neg_energy'`](https://prove2.me/theorems/12ffe5ab-1e01-479f-819d-012727f89a87)
--   - [`integrable_weak_generator_densities`](https://prove2.me/theorems/24449bc6-0de3-4efc-93a6-7a73a3bded73)
--   - [`hasWeakDerivAlong_inverse_hessian_of_logdet`](https://prove2.me/theorems/6e913d0c-8e93-456f-8534-533355d49266)
--   - [`integral_mul_generator_eq_neg_energy_of_contDiff_one`](https://prove2.me/theorems/bda30b6e-bb4c-453a-b213-90c9b1d32698)
--   - [`ae_inverse_hessian_row_divergence_of_weak_derivative`](https://prove2.me/theorems/e773702c-7809-4847-beb6-e121927d46e0)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean) · `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L383-L402 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Star

noncomputable section
section GeneratorIdentities
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities
namespace Analysis
 abbrev coord {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)
 def weightedTest {n : ℕ}
    (u a f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a x * Real.exp (-u x) * FunctionalInequalities.Analysis.coord f i x
 def energyDensity {n : ℕ}
    (u a f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j * FunctionalInequalities.Analysis.coord a i x * FunctionalInequalities.Analysis.coord f j x) *
    Real.exp (-u x)
 def generatorDensity {n : ℕ}
    (u V a f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a x * (((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace -
    fderiv ℝ V (gradient u x) (gradient f x)) * Real.exp (-u x)
end Analysis
end FunctionalInequalities
end GeneratorIdentities


